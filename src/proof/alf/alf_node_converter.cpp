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
  if (k == ASCRIPTION_TYPE)
  {
    // dummy node, return it
    return n;
  }
  TypeNode tn = n.getType();
  Trace("alf-term-process-debug")
      << "postConvert " << n << " " << k << std::endl;
  if (k == BOUND_VARIABLE || k == RAW_SYMBOL)
  {
    return n;
  }
  else if (k == SKOLEM)
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
    TypeNode intType = nm->integerType();
    TypeNode varType = nm->mkFunctionType({intType, d_sortType}, tn);
    Node var = mkInternalSymbol("var", varType);
    Node index = nm->mkConstInt(Rational(getOrAssignIndexForFVar(n)));
    Node tc = typeAsNode(convertType(tn));
    return mkApplyUf(var, {index, tc});
  }
  else if (k == CONST_INTEGER)
  {
    Rational r = n.getConst<Rational>();
    if (r.sgn() == -1)
    {
      Node na = nm->mkConstInt(r.abs());
      Node intNeg = getSymbolInternal(k, nm->mkFunctionType(tn, tn), "alf.neg");
      return mkApplyUf(intNeg, {na});
    }
    return n;
  }
  else if (k == CONST_RATIONAL)
  {
    TypeNode tnv = nm->mkFunctionType({tn, tn}, tn);
    Rational r = n.getConst<Rational>();
    Node realDiv = getSymbolInternal(k, tnv, "alf.qdiv");
    // ensure rationals are printed properly here using alf syntax
    // which computes the rational (alf.qdiv n d).
    Node num = nm->mkConstInt(r.getNumerator().abs());
    Node den = nm->mkConstInt(r.getDenominator());
    Node ret = mkApplyUf(realDiv, {num, den});
    // negative (alf.neg .)
    if (r.sgn() == -1)
    {
      Node realNeg =
          getSymbolInternal(k, nm->mkFunctionType(tn, tn), "alf.neg");
      ret = mkApplyUf(realNeg, {ret});
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
      Node v = n[0][ii];
      // use the body return type for all terms except the last one.
      TypeNode retType = ii == 0 ? n.getType() : n[1].getType();
      TypeNode ftype =
          nm->mkFunctionType({v.getType(), ret.getType()}, retType);
      Node vop = getSymbolInternal(k, ftype, opName.str());
      ret = mkApplyUf(vop, {v, ret});
    }
    // notice that intentionally we drop annotations here
    return ret;
  }
  else if (k == FUNCTION_ARRAY_CONST)
  {
    // must convert to lambda and then run the conversion
    Node lam = theory::uf::FunctionConst::toLambda(n);
    Assert(!lam.isNull());
    return convert(lam);
  }
  else if (k == APPLY_TESTER || k == APPLY_UPDATER || k == NEG)
  {
    // kinds where the operator may be different
    Node opc = getOperatorOfTerm(n);
    return mkApplyUf(opc, std::vector<Node>(n.begin(), n.end()));
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

std::string AlfNodeConverter::getNameForUserName(const std::string& name,
                                                 size_t variant)
{
  // For user name X, we do cvc.Y, where Y contains an escaped version of X.
  // Specifically, since LFSC does not allow these characters in identifier
  // bodies: "() \t\n\f;", each is replaced with an escape sequence "\xXX"
  // where XX is the zero-padded hex representation of the code point. "\\" is
  // also escaped.
  //
  // See also: https://github.com/cvc5/LFSC/blob/master/src/lexer.flex#L24
  //
  // The "cvc." prefix ensures we do not clash with LFSC definitions.
  //
  // The escaping ensures that all names are valid LFSC identifiers.
  std::stringstream ss;
  ss << "cvc";
  if (variant != 0)
  {
    ss << variant;
  }
  ss << ".";
  std::string sanitized = ss.str();
  size_t found = sanitized.size();
  sanitized += name;
  // The following sanitizes symbols that are not allowed in LFSC identifiers
  // here, e.g.
  //   |a b|
  // is converted to:
  //   cvc.a\x20b
  // where "20" is the hex unicode value of " ".
  do
  {
    found = sanitized.find_first_of("() \t\n\f\\;", found);
    if (found != std::string::npos)
    {
      // Emit hex sequence
      std::stringstream seq;
      seq << "\\x" << std::setbase(16) << std::setfill('0') << std::setw(2)
          << static_cast<size_t>(sanitized[found]);
      sanitized.replace(found, 1, seq.str());
      // increment found over the escape
      found += 3;
    }
  } while (found != std::string::npos);
  return sanitized;
}

std::string AlfNodeConverter::getNameForUserNameOf(Node v)
{
  std::string name = v.getName();
  return getNameForUserNameOfInternal(v.getId(), name);
}

std::string AlfNodeConverter::getNameForUserNameOfInternal(
    uint64_t id, const std::string& name)
{
  std::vector<uint64_t>& syms = d_userSymbolList[name];
  size_t variant = 0;
  std::vector<uint64_t>::iterator itr = std::find(syms.begin(), syms.end(), id);
  if (itr != syms.cend())
  {
    variant = std::distance(syms.begin(), itr);
  }
  else
  {
    variant = syms.size();
    syms.push_back(id);
  }
  return getNameForUserName(name, variant);
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
      else
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
  std::stringstream ss;
  ss << tn;
  Node ret = mkInternalSymbol(ss.str(), d_sortType, true);
  d_typeAsNode[tn] = ret;
  return ret;
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

Node AlfNodeConverter::getSymbolInternalFor(Node n,
                                            const std::string& name,
                                            bool useRawSym)
{
  return getSymbolInternal(n.getKind(), n.getType(), name, useRawSym);
}

Node AlfNodeConverter::getSymbolInternal(Kind k,
                                         TypeNode tn,
                                         const std::string& name,
                                         bool useRawSym)
{
  std::tuple<Kind, TypeNode, std::string> key(k, tn, name);
  std::map<std::tuple<Kind, TypeNode, std::string>, Node>::iterator it =
      d_symbolsMap.find(key);
  if (it != d_symbolsMap.end())
  {
    return it->second;
  }
  Node sym = mkInternalSymbol(name, tn, useRawSym);
  d_symbolToBuiltinKind[sym] = k;
  d_symbolsMap[key] = sym;
  return sym;
}

Node AlfNodeConverter::getNullTerminator(Kind k, TypeNode tn)
{
  return getSymbolInternal(k, tn, "alf.nil");
}

Kind AlfNodeConverter::getBuiltinKindForInternalSymbol(Node op) const
{
  std::map<Node, Kind>::const_iterator it = d_symbolToBuiltinKind.find(op);
  if (it != d_symbolToBuiltinKind.end())
  {
    return it->second;
  }
  return UNDEFINED_KIND;
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
    if (k == APPLY_UPDATER || k == APPLY_TESTER)
    {
      // TODO: is-C or update-S.
    }
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
      std::vector<TypeNode> itypes;
      for (const Node& i : indices)
      {
        itypes.push_back(i.getType());
      }
      if (!itypes.empty())
      {
        ftype = nm->mkFunctionType(itypes, ftype);
      }
      // must avoid overloading for to_fp variants
      if (k == FLOATINGPOINT_TO_FP_FROM_FP)
      {
        opName << "to_fp_fp";
      }
      else if (k == FLOATINGPOINT_TO_FP_FROM_IEEE_BV)
      {
        opName << "to_fp_ieee_bv";
      }
      else if (k == FLOATINGPOINT_TO_FP_FROM_SBV)
      {
        opName << "to_fp_sbv";
      }
      else if (k == FLOATINGPOINT_TO_FP_FROM_REAL)
      {
        opName << "to_fp_real";
      }
      else
      {
        opName << printer::smt2::Smt2Printer::smtKindString(k);
      }
    }
    else if (k == APPLY_CONSTRUCTOR)
    {
      unsigned index = DType::indexOf(op);
      const DType& dt = DType::datatypeOf(op);
      // get its variable name
      opName << getNameForUserNameOf(dt[index].getConstructor());
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
        opName << getNameForUserNameOf(dt[cindex][index].getSelector());
      }
    }
    else if (k == SET_SINGLETON || k == BAG_MAKE || k == SEQ_UNIT)
    {
      opName << printer::smt2::Smt2Printer::smtKindString(k);
    }
    else
    {
      opName << op;
    }
    if (ret.isNull())
    {
      Trace("alf-term-process-debug2") << "...default symbol" << std::endl;
      ret = getSymbolInternal(k, ftype, opName.str());
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
  return getSymbolInternal(k, ftype, opName.str());
}

size_t AlfNodeConverter::getOrAssignIndexForFVar(Node fv)
{
  Assert(fv.isVar());
  std::map<Node, size_t>::iterator it = d_fvarIndex.find(fv);
  if (it != d_fvarIndex.end())
  {
    return it->second;
  }
  size_t id = d_fvarIndex.size();
  d_fvarIndex[fv] = id;
  return id;
}

}  // namespace proof
}  // namespace cvc5::internal
