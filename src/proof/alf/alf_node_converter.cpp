/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of LFSC node conversion
 */

#include "proof/alf/alf_node_converter.h"

#include <algorithm>
#include <iomanip>
#include <sstream>

#include "expr/array_store_all.h"
#include "expr/cardinality_constraint.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/nary_term_util.h"
#include "expr/sequence.h"
#include "expr/skolem_manager.h"
#include "printer/smt2/smt2_printer.h"
#include "theory/builtin/generic_op.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/strings/word.h"
#include "theory/uf/function_const.h"
#include "theory/uf/theory_uf_rewriter.h"
#include "util/bitvector.h"
#include "util/finite_field_value.h"
#include "util/floatingpoint.h"
#include "util/iand.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace proof {

AlfNodeConverter::AlfNodeConverter()
{
  NodeManager* nm = NodeManager::currentNM();
  d_sortType = nm->mkSort("sortType");
}

Node AlfNodeConverter::preConvert(Node n)
{
  // match is not supported in LFSC syntax, we eliminate it at pre-order
  // traversal, which avoids type-checking errors during conversion, since e.g.
  // match case nodes are required but cannot be preserved
  if (n.getKind() == MATCH)
  {
    return theory::datatypes::DatatypesRewriter::expandMatch(n);
  }
  return n;
}

Node AlfNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  // we eliminate MATCH at preConvert above
  Assert(k != MATCH);
  if (k == ASCRIPTION_TYPE || k == RAW_SYMBOL)
  {
    // dummy node, return it
    return n;
  }
  TypeNode tn = n.getType();
  Trace("alf-term-process-debug")
      << "postConvert " << n << " " << k << std::endl;
  if (k == SKOLEM)
  {
    // constructors/selectors are represented by skolems, which are defined
    // symbols
    if (tn.isDatatypeConstructor() || tn.isDatatypeSelector()
        || tn.isDatatypeTester() || tn.isDatatypeUpdater())
    {
      // note these are not converted to their user named (cvc.) symbols here,
      // to avoid type errors when constructing terms for postConvert
      return n;
    }
    // might be a skolem function
    Node ns = maybeMkSkolemFun(n);
    if (!ns.isNull())
    {
      return ns;
    }
    // Otherwise, it is an uncategorized skolem, must use a fresh variable.
    // This case will only apply for terms originating from places with no
    // proof support. Note it is not added as a declared variable, instead it
    // is used as (var N T) throughout.
    Node index = nm->mkConstInt(Rational(getOrAssignIndexForConst(n)));
    Node tc = typeAsNode(tn);
    return mkInternalApp("const", {index, tc}, tn);
  }
  else if (k==BOUND_VARIABLE)
  {
    std::stringstream ss;
    ss << n;
    std::string sname = ss.str();
    size_t index = d_varIndex[sname];
    if (index==0)
    {
      return n;
    }
    std::stringstream ssn;
    ssn << "alf.var" << index << "." << sname;
    return NodeManager::currentNM()->mkBoundVar(ssn.str(), tn);
  }
  else if (k == APPLY_UF)
  {
    // must ensure we print higher-order function applications with "_"
    if (!n.getOperator().isVar())
    {
      std::vector<Node> args;
      args.push_back(n.getOperator());
      args.insert(args.end(), n.begin(), n.end());
      return mkInternalApp("_", args, tn);
    }
  }
  else if (k == HO_APPLY)
  {
    return mkInternalApp("_", {n[0], n[1]}, tn);
  }
  else if (k == CONST_INTEGER)
  {
    Rational r = n.getConst<Rational>();
    if (r.sgn() == -1)
    {
      Node na = nm->mkConstInt(r.abs());
      return mkInternalApp("alf.neg", {na}, tn);
    }
    return n;
  }
  else if (k == CONST_RATIONAL)
  {
    Rational r = n.getConst<Rational>();
    // ensure rationals are printed properly here using alf syntax
    // which computes the rational (alf.qdiv n d).
    Node num = nm->mkConstInt(r.getNumerator().abs());
    Node den = nm->mkConstInt(r.getDenominator());
    Node ret = mkInternalApp("alf.qdiv", {num, den}, tn);
    // negative (alf.neg .)
    if (r.sgn() == -1)
    {
      ret = mkInternalApp("alf.neg", {ret}, tn);
    }
    return ret;
  }
  else if (n.isClosure())
  {
    // e.g. (forall ((x1 T1) ... (xn Tk)) P) is
    // (forall x1 (forall x2 ... (forall xn P)))
    Node ret = n[1];
    std::stringstream opName;
    opName << printer::smt2::Smt2Printer::smtKindString(k);
    for (size_t i = 0, nchild = n[0].getNumChildren(); i < nchild; i++)
    {
      size_t ii = (nchild - 1) - i;
      Node v = convert(n[0][ii]);
      // use the body return type for all terms except the last one.
      TypeNode retType = ii == 0 ? n.getType() : n[1].getType();
      ret = mkInternalApp(opName.str(), {v, ret}, retType);
    }
    // notice that intentionally we drop annotations here
    return ret;
  }
  else if (k == STORE_ALL)
  {
    Node t = typeAsNode(tn);
    ArrayStoreAll storeAll = n.getConst<ArrayStoreAll>();
    Node val = convert(storeAll.getValue());
    return mkInternalApp("store_all", {t, val}, tn);
  }
  else if (k == SET_EMPTY || k == SET_UNIVERSE || k == BAG_EMPTY)
  {
    Node t = typeAsNode(tn);
    return mkInternalApp(printer::smt2::Smt2Printer::smtKindString(k), {t}, tn);
  }
  else if (k == CONST_FINITE_FIELD)
  {
    const FiniteFieldValue& ffv = n.getConst<FiniteFieldValue>();
    Node v = convert(nm->mkConstInt(ffv.getValue()));
    Node fs = convert(nm->mkConstInt(ffv.getFieldSize()));
    return mkInternalApp("ff.value", {fs, v}, tn);
  }
  else if (k == FUNCTION_ARRAY_CONST)
  {
    // must convert to lambda and then run the conversion
    Node lam = theory::uf::FunctionConst::toLambda(n);
    Assert(!lam.isNull());
    return convert(lam);
  }
  else if (k==BITVECTOR_BB_TERM)
  {
    Node curr = mkInternalSymbol("bvempty", nm->mkBitVectorType(0));
    for (size_t i=0, nchildren=n.getNumChildren(); i<nchildren; i++)
    {
      size_t ii = (nchildren-1)-i;
      std::vector<Node> args;
      args.push_back(n[ii]);
      args.push_back(curr);
      curr = mkInternalApp("bbT", args, nm->mkBitVectorType(i+1));
    }
    return curr;
  }
  else if (k == APPLY_TESTER || k == APPLY_UPDATER || k == NEG
           || k == DIVISION_TOTAL || k == INTS_DIVISION_TOTAL
           || k == INTS_MODULUS_TOTAL)
  {
    // kinds where the operator may be different
    Node opc = getOperatorOfTerm(n);
    return mkApplyUf(opc, std::vector<Node>(n.begin(), n.end()));
  }
  else if (GenericOp::isIndexedOperatorKind(k))
  {
    // return app of?
    std::vector<Node> args =
        GenericOp::getIndicesForOperator(k, n.getOperator());
    args.insert(args.end(), n.begin(), n.end());
    return mkInternalApp(
        printer::smt2::Smt2Printer::smtKindString(k), args, n.getType());
  }
  return n;
}

Node AlfNodeConverter::mkApplyUf(Node op, const std::vector<Node>& args) const
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> aargs;
  if (op.isVar())
  {
    aargs.push_back(op);
  }
  else
  {
    // Note that dag threshold is disabled for printing operators.
    std::stringstream ss;
    options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
    options::ioutils::applyDagThresh(ss, 0);
    ss << op;
    Node opv = nm->mkRawSymbol(ss.str(), op.getType());
    aargs.push_back(opv);
  }
  aargs.insert(aargs.end(), args.begin(), args.end());
  return nm->mkNode(APPLY_UF, aargs);
}

bool AlfNodeConverter::shouldTraverse(Node n)
{
  Kind k = n.getKind();
  // don't convert bound variable or instantiation pattern list directly
  if (k == BOUND_VAR_LIST || k == INST_PATTERN_LIST)
  {
    return false;
  }
  // should not traverse internal applications
  if (k == APPLY_UF)
  {
    if (d_symbols.find(n.getOperator()) != d_symbols.end())
    {
      return false;
    }
  }
  return true;
}

Node AlfNodeConverter::maybeMkSkolemFun(Node k)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  SkolemFunId sfi = SkolemFunId::NONE;
  Node cacheVal;
  TypeNode tn = k.getType();
  if (sm->isSkolemFunction(k, sfi, cacheVal))
  {
    Node app;
    if (sfi == SkolemFunId::PURIFY)
    {
      Assert(cacheVal.getType() == k.getType());
      // special case: just use self
      app = convert(cacheVal);
    }
    else
    {
      // convert every skolem function to its name applied to arguments
      std::stringstream ss;
      ss << "@k." << sfi;
      std::vector<Node> args;
      if (cacheVal.getKind() == SEXPR)
      {
        for (const Node& cv : cacheVal)
        {
          args.push_back(convert(cv));
        }
      }
      else if (!cacheVal.isNull())
      {
        args.push_back(convert(cacheVal));
      }
      // must convert all arguments
      app = mkInternalApp(ss.str(), args, k.getType());
    }
    // wrap in "skolem" operator
    return mkInternalApp("skolem", {app}, k.getType());
  }
  return Node::null();
}

Node AlfNodeConverter::typeAsNode(TypeNode tn)
{
  // should always exist in the cache, as we always run types through
  // postConvertType before calling this method.
  std::map<TypeNode, Node>::const_iterator it = d_typeAsNode.find(tn);
  if (it != d_typeAsNode.end())
  {
    return it->second;
  }
  // dummy symbol whose name is the type printed
  // this suffices since ALF faithfully represents all types.
  // note we cannot letify types (same as in SMT-LIB)
  std::stringstream ss;
  ss << tn;
  Node ret = mkInternalSymbol(ss.str(), d_sortType, true);
  d_typeAsNode[tn] = ret;
  return ret;
}

Node AlfNodeConverter::mkNil(TypeNode tn)
{
  return mkInternalSymbol("alf.nil", tn);
}

Node AlfNodeConverter::getNullTerminator(Kind k, TypeNode tn)
{
  switch (k)
  {
    case kind::ADD:
      return NodeManager::currentNM()->mkConstInt(Rational(0));
    case kind::MULT:
    case kind::NONLINEAR_MULT:
      return NodeManager::currentNM()->mkConstInt(Rational(1));
    case kind::BITVECTOR_CONCAT:
      return mkInternalSymbol("bvempty", NodeManager::currentNM()->mkBitVectorType(0));
    case kind::BITVECTOR_BB_TERM:
      return NodeManager::currentNM()->mkConst(true);
    default:
      break;
  }
  return mkNil(tn);
}

Node AlfNodeConverter::mkSExpr(const std::vector<Node>& args)
{
  TypeNode tn = NodeManager::currentNM()->booleanType();
  if (args.empty())
  {
    return mkNil(tn);
  }
  else if (args.size()==1)
  {
    std::vector<Node> aargs(args.begin(), args.end());
    aargs.push_back(mkNil(tn));
    return mkInternalApp("sexpr", aargs, tn);
  }
    return mkInternalApp("sexpr", args, tn);
}

Node AlfNodeConverter::mkInternalSymbol(const std::string& name,
                                        TypeNode tn,
                                        bool useRawSym)
{
  // use raw symbol so that it is never quoted
  NodeManager* nm = NodeManager::currentNM();
  Node sym = useRawSym ? nm->mkRawSymbol(name, tn) : nm->mkBoundVar(name, tn);
  d_symbols.insert(sym);
  return sym;
}

Node AlfNodeConverter::mkInternalApp(const std::string& name,
                                     const std::vector<Node>& args,
                                     TypeNode ret,
                                     bool useRawSym)
{
  if (!args.empty())
  {
    std::vector<TypeNode> argTypes;
    for (const Node& a : args)
    {
      Assert (!a.isNull());
      argTypes.push_back(a.getType());
    }
    NodeManager* nm = NodeManager::currentNM();
    TypeNode atype = nm->mkFunctionType(argTypes, ret);
    Node op = mkInternalSymbol(name, atype, useRawSym);
    std::vector<Node> aargs;
    aargs.push_back(op);
    aargs.insert(aargs.end(), args.begin(), args.end());
    return nm->mkNode(APPLY_UF, aargs);
  }
  return mkInternalSymbol(name, ret, useRawSym);
}

Node AlfNodeConverter::getOperatorOfTerm(Node n)
{
  Assert(n.hasOperator());
  Assert(!n.isClosure());
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  std::stringstream opName;
  Trace("alf-term-process-debug2")
      << "getOperatorOfTerm " << n << " " << k << " "
      << (n.getMetaKind() == metakind::PARAMETERIZED) << " "
      << GenericOp::isIndexedOperatorKind(k) << std::endl;
  if (n.getMetaKind() == metakind::PARAMETERIZED)
  {
    Node op = n.getOperator();
    std::vector<Node> indices;
    bool isIndexed = GenericOp::isIndexedOperatorKind(k);
    if (isIndexed)
    {
      indices = GenericOp::getIndicesForOperator(k, n.getOperator());
    }
    else if (op.getType().isFunction())
    {
      return op;
    }
    // note other kinds of functions (e.g. selectors and testers)
    std::vector<TypeNode> argTypes;
    for (const Node& nc : n)
    {
      argTypes.push_back(nc.getType());
    }
    TypeNode ftype = n.getType();
    if (!argTypes.empty())
    {
      ftype = nm->mkFunctionType(argTypes, ftype);
    }
    Node ret;
    if (isIndexed)
    {
      if (k == APPLY_TESTER)
      {
        size_t cindex = DType::indexOf(op);
        const DType& dt = DType::datatypeOf(op);
        opName << "is-" << dt[cindex].getConstructor();
        indices.clear();
      }
      else if (k == APPLY_UPDATER)
      {
        size_t index = DType::indexOf(op);
        const DType& dt = DType::datatypeOf(op);
        size_t cindex = DType::cindexOf(op);
        if (dt.isTuple())
        {
          opName << "tuple.update";
        }
        else
        {
          opName << "update-" << dt[cindex][index].getSelector();
        }
        indices.clear();
      }
      else
      {
        std::vector<TypeNode> itypes;
        for (const Node& i : indices)
        {
          itypes.push_back(i.getType());
        }
        if (!itypes.empty())
        {
          ftype = nm->mkFunctionType(itypes, ftype);
        }
        opName << printer::smt2::Smt2Printer::smtKindString(k);
      }
    }
    else if (k == APPLY_CONSTRUCTOR)
    {
      unsigned index = DType::indexOf(op);
      const DType& dt = DType::datatypeOf(op);
      // get its variable name
      opName << dt[index].getConstructor();
    }
    else if (k == APPLY_SELECTOR)
    {
      // maybe a shared selector
      ret = maybeMkSkolemFun(op);
      if (ret.isNull())
      {
        unsigned index = DType::indexOf(op);
        const DType& dt = DType::datatypeOf(op);
        unsigned cindex = DType::cindexOf(op);
        opName << dt[cindex][index].getSelector();
      }
    }
    else
    {
      opName << op;
    }
    if (ret.isNull())
    {
      Trace("alf-term-process-debug2") << "...default symbol" << std::endl;
      ret = mkInternalSymbol(opName.str(), ftype);
    }
    // if indexed, apply to index
    if (!indices.empty())
    {
      ret = mkApplyUf(ret, indices);
    }
    Trace("alf-term-process-debug2") << "...return " << ret << std::endl;
    return ret;
  }
  std::vector<TypeNode> argTypes;
  for (const Node& nc : n)
  {
    argTypes.push_back(nc.getType());
  }
  // we only use binary operators
  if (NodeManager::isNAryKind(k))
  {
    argTypes.resize(2);
  }
  TypeNode tn = n.getType();
  TypeNode ftype = nm->mkFunctionType(argTypes, tn);
  if (k == NEG)
  {
    opName << "u";
  }
  opName << printer::smt2::Smt2Printer::smtKindString(k);
  if (k == DIVISION_TOTAL || k == INTS_DIVISION_TOTAL
      || k == INTS_MODULUS_TOTAL)
  {
    opName << "_total";
  }
  return mkInternalSymbol(opName.str(), ftype);
}

size_t AlfNodeConverter::getOrAssignIndexForConst(Node v)
{
  Assert(v.isVar());
  std::map<Node, size_t>::iterator it = d_constIndex.find(v);
  if (it != d_constIndex.end())
  {
    return it->second;
  }
  size_t id = d_constIndex.size();
  d_constIndex[v] = id;
  return id;
}

}  // namespace proof
}  // namespace cvc5::internal
