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

  TypeNode intType = nm->integerType();
  TypeNode arrType = nm->mkFunctionType({d_sortType, d_sortType}, d_sortType);
  d_typeKindToNodeCons[ARRAY_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, arrType, "Array");
  TypeNode bvType = nm->mkFunctionType(intType, d_sortType);
  d_typeKindToNodeCons[BITVECTOR_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, bvType, "BitVec");
  TypeNode fpType = nm->mkFunctionType({intType, intType}, d_sortType);
  d_typeKindToNodeCons[FLOATINGPOINT_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, fpType, "FloatingPoint");
  TypeNode setType = nm->mkFunctionType(d_sortType, d_sortType);
  d_typeKindToNodeCons[SET_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, setType, "Set");
  d_typeKindToNodeCons[BAG_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, setType, "Bag");
  d_typeKindToNodeCons[SEQUENCE_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, setType, "Seq");
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
  if (k == BOUND_VARIABLE)
  {
    return n;
  }
  else if (k == RAW_SYMBOL)
  {
    // ignore internally generated symbols
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
    // skolems v print as their original forms
    // v is (skolem W) where W is the original or original form of v
    Node wi = SkolemManager::getUnpurifiedForm(n);
    if (!wi.isNull() && wi != n)
    {
      Trace("alf-term-process-debug") << "...original form " << wi << std::endl;
      wi = convert(wi);
      Trace("alf-term-process-debug")
          << "...converted original for " << wi << std::endl;
      TypeNode ftype = nm->mkFunctionType(tn, tn);
      Node skolemOp = getSymbolInternal(k, ftype, "skolem");
      return mkApplyUf(skolemOp, {wi});
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
    // FIXME
    TypeNode intType = nm->integerType();
    TypeNode varType = nm->mkFunctionType({intType, d_sortType}, tn);
    Node var = mkInternalSymbol("var", varType);
    Node index = nm->mkConstInt(Rational(getOrAssignIndexForFVar(n)));
    Node tc = typeAsNode(convertType(tn));
    return mkApplyUf(var, {index, tc});
  }
  else if (n.isVar())
  {
    return mkInternalSymbol(getNameForUserNameOf(n), tn);
  }
  else if (k == CARDINALITY_CONSTRAINT)
  {
    Trace("alf-term-process-debug")
        << "...convert cardinality constraint" << std::endl;
    const CardinalityConstraint& cc =
        n.getOperator().getConst<CardinalityConstraint>();
    Node tnn = typeAsNode(convertType(cc.getType()));
    Node ub = nm->mkConstInt(Rational(cc.getUpperBound()));
    TypeNode tnc =
        nm->mkFunctionType({tnn.getType(), ub.getType()}, nm->booleanType());
    Node fcard = getSymbolInternal(k, tnc, "fmf.card");
    return mkApplyUf(fcard, {tnn, ub});
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
    // (forall ((x1 T1) ... (xn Tk)) P) is
    // (forall x1 (forall x2 ... (forall xn P)))
    Node ret = n[1];
    std::stringstream opName;
    opName << printer::smt2::Smt2Printer::smtKindString(k);
    for (size_t i = 0, nchild = n[0].getNumChildren(); i < nchild; i++)
    {
      size_t ii = (nchild - 1) - i;
      Node v = n[0][ii];
      // use the body return type for all terms except the last one.
      TypeNode retType = ii==0 ? n.getType() : n[1].getType();
      TypeNode ftype = nm->mkFunctionType({v.getType(), ret.getType()}, retType);
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
  else if (k == REGEXP_LOOP)
  {
    // ((_ re.loop n1 n2) t) is ((re.loop n1 n2) t)
    TypeNode intType = nm->integerType();
    TypeNode relType =
        nm->mkFunctionType({intType, intType}, nm->mkFunctionType(tn, tn));
    Node rop = getSymbolInternal(
        k, relType, printer::smt2::Smt2Printer::smtKindString(k));
    RegExpLoop op = n.getOperator().getConst<RegExpLoop>();
    Node n1 = nm->mkConstInt(Rational(op.d_loopMinOcc));
    Node n2 = nm->mkConstInt(Rational(op.d_loopMaxOcc));
    return mkApplyUf(mkApplyUf(rop, {n1, n2}), {n[0]});
  }
  else if (k == SEP_NIL)
  {
    Node tnn = typeAsNode(convertType(tn));
    TypeNode ftype = nm->mkFunctionType(d_sortType, tn);
    Node s = getSymbolInternal(k, ftype, "sep.nil");
    return mkApplyUf(s, {tnn});
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

TypeNode AlfNodeConverter::preConvertType(TypeNode tn) { return tn; }

TypeNode AlfNodeConverter::postConvertType(TypeNode tn)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode cur = tn;
  Node tnn;
  Kind k = tn.getKind();
  Trace("alf-term-process-debug")
      << "postConvertType " << tn << " " << tn.getNumChildren() << " " << k
      << std::endl;
  if (k == BITVECTOR_TYPE)
  {
    tnn = d_typeKindToNodeCons[k];
    Node w = nm->mkConstInt(Rational(tn.getBitVectorSize()));
    tnn = mkApplyUf(tnn, {w});
  }
  else if (k == FLOATINGPOINT_TYPE)
  {
    tnn = d_typeKindToNodeCons[k];
    Node e = nm->mkConstInt(Rational(tn.getFloatingPointExponentSize()));
    Node s = nm->mkConstInt(Rational(tn.getFloatingPointSignificandSize()));
    tnn = mkApplyUf(tnn, {e, s});
  }
  else if (k == TUPLE_TYPE)
  {
    // special case: tuples must be distinguished by their arity
    size_t nargs = tn.getNumChildren();
    if (nargs > 0)
    {
      std::vector<TypeNode> types;
      std::vector<TypeNode> convTypes;
      std::vector<Node> targs;
      for (size_t i = 0; i < nargs; i++)
      {
        TypeNode tnc = tn[i];
        types.push_back(d_sortType);
        convTypes.push_back(tnc);
        targs.push_back(typeAsNode(tnc));
      }
      TypeNode ftype = nm->mkFunctionType(types, d_sortType);
      // must distinguish by arity
      std::stringstream ss;
      ss << "Tuple_" << nargs;
      tnn = mkApplyUf(getSymbolInternal(k, ftype, ss.str()), targs);
      // we are changing its name, we must make a sort constructor
      cur = nm->mkSortConstructor(ss.str(), nargs);
      cur = nm->mkSort(cur, convTypes);
    }
    else
    {
      // no need to convert type for tuples of size 0,
      // type as node is simple
      tnn = getSymbolInternal(k, d_sortType, "Tuple");
    }
  }
  else if (tn.getNumChildren() == 0)
  {
    Assert(!tn.isTuple());
    // an uninterpreted sort, or an uninstantiatied (maybe parametric) datatype
    std::stringstream ss;
    options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
    tn.toStream(ss);
    if (tn.isUninterpretedSortConstructor())
    {
      std::string s = getNameForUserNameOfInternal(tn.getId(), ss.str());
      tnn = getSymbolInternal(k, d_sortType, s, false);
      cur = nm->mkSortConstructor(s, tn.getUninterpretedSortConstructorArity());
    }
    else if (tn.isUninterpretedSort() || tn.isDatatype())
    {
      std::string s = getNameForUserNameOfInternal(tn.getId(), ss.str());
      tnn = getSymbolInternal(k, d_sortType, s, false);
      cur = nm->mkSort(s);
    }
    else
    {
      // all other builtin type constants, e.g. Int
      tnn = getSymbolInternal(k, d_sortType, ss.str());
    }
  }
  else
  {
    // to build the type-as-node, must convert the component types
    std::vector<Node> targs;
    std::vector<TypeNode> types;
    for (const TypeNode& tnc : tn)
    {
      targs.push_back(typeAsNode(tnc));
      types.push_back(d_sortType);
    }
    Node op;
    if (k == PARAMETRIC_DATATYPE)
    {
      // note we don't add to declared types here, since the parametric
      // datatype is traversed and will be declared as a type constructor
      // erase first child, which repeats the datatype
      targs.erase(targs.begin(), targs.begin() + 1);
      types.erase(types.begin(), types.begin() + 1);
      TypeNode ftype = nm->mkFunctionType(types, d_sortType);
      // the operator has been converted; it is no longer a datatype, thus
      // we must print to get its name.
      std::stringstream ss;
      ss << tn[0];
      op = getSymbolInternal(k, ftype, ss.str());
    }
    else if (k == INSTANTIATED_SORT_TYPE)
    {
      // We don't add to declared types here. The type constructor is already
      // added to declare types when processing the children of this.
      // Also, similar to PARAMETRIC_DATATYPE, the type constructor
      // should be erased from children.
      targs.erase(targs.begin(), targs.begin() + 1);
      types.erase(types.begin(), types.begin() + 1);
      TypeNode ftype = nm->mkFunctionType(types, d_sortType);
      std::string name = tn.getUninterpretedSortConstructor().getName();
      op = getSymbolInternal(k, ftype, name, false);
    }
    else if (k == FUNCTION_TYPE)
    {
      TypeNode ftype = nm->mkFunctionType(types, d_sortType);
      op = getSymbolInternal(k, ftype, "->");
    }
    else
    {
      std::map<Kind, Node>::iterator it = d_typeKindToNodeCons.find(k);
      if (it != d_typeKindToNodeCons.end())
      {
        op = it->second;
      }
    }
    if (!op.isNull())
    {
      tnn = mkApplyUf(op, targs);
    }
    else
    {
      AlwaysAssert(false);
    }
  }
  Assert(!tnn.isNull());
  Trace("alf-term-process-debug") << "...type as node: " << tnn << std::endl;
  d_typeAsNode[cur] = tnn;
  return cur;
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
    if (sfi == SkolemFunId::SHARED_SELECTOR)
    {
      // a skolem corresponding to shared selector should print in
      // LFSC as (sel T n) where T is the type and n is the index of the
      // shared selector.
      TypeNode fselt = nm->mkFunctionType(tn.getDatatypeSelectorDomainType(),
                                          tn.getDatatypeSelectorRangeType());
      TypeNode intType = nm->integerType();
      TypeNode selt = nm->mkFunctionType({d_sortType, intType}, fselt);
      Node sel = getSymbolInternal(k.getKind(), selt, "sel");
      Node kn = typeAsNode(convertType(tn.getDatatypeSelectorRangeType()));
      Assert(!cacheVal.isNull() && cacheVal.getKind() == CONST_RATIONAL);
      return mkApplyUf(sel, {kn, cacheVal});
    }
    else if (sfi == SkolemFunId::RE_UNFOLD_POS_COMPONENT)
    {
      // a skolem corresponding to a regular expression unfolding component
      // should print as (skolem_re_unfold_pos t R n) where the skolem is the
      // n^th component for the unfolding of (str.in_re t R).
      TypeNode strType = nm->stringType();
      TypeNode reType = nm->regExpType();
      TypeNode intType = nm->integerType();
      TypeNode reut = nm->mkFunctionType({strType, reType, intType}, strType);
      Node sk = getSymbolInternal(k.getKind(), reut, "skolem_re_unfold_pos");
      Assert(!cacheVal.isNull() && cacheVal.getKind() == SEXPR
             && cacheVal.getNumChildren() == 3);
      // third value is mpz, which is not converted
      return mkApplyUf(
          sk, {convert(cacheVal[0]), convert(cacheVal[1]), cacheVal[2]});
    }
  }
  return Node::null();
}

Node AlfNodeConverter::typeAsNode(TypeNode tni) const
{
  // should always exist in the cache, as we always run types through
  // postConvertType before calling this method.
  std::map<TypeNode, Node>::const_iterator it = d_typeAsNode.find(tni);
  AlwaysAssert(it != d_typeAsNode.end()) << "Missing typeAsNode " << tni;
  return it->second;
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

void AlfNodeConverter::getCharVectorInternal(Node c, std::vector<Node>& chars)
{
  Assert(c.getKind() == CONST_STRING);
  NodeManager* nm = NodeManager::currentNM();
  const std::vector<unsigned>& vec = c.getConst<String>().getVec();
  if (vec.size() == 0)
  {
    Node ec = getSymbolInternalFor(c, "emptystr");
    chars.push_back(ec);
    return;
  }
  TypeNode tnc = nm->mkFunctionType(nm->integerType(), c.getType());
  Node aconstf = getSymbolInternal(CONST_STRING, tnc, "char");
  for (unsigned i = 0, size = vec.size(); i < size; i++)
  {
    Node cc = mkApplyUf(aconstf, {nm->mkConstInt(Rational(vec[i]))});
    chars.push_back(cc);
  }
}

Node AlfNodeConverter::convertBitVector(const BitVector& bv)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode btn = nm->booleanType();
  TypeNode btnv = nm->mkFunctionType({btn, btn}, btn);
  size_t w = bv.getSize();
  Node ret = getSymbolInternal(CONST_BITVECTOR, btn, "bvn");
  Node b0 = getSymbolInternal(CONST_BITVECTOR, btn, "b0");
  Node b1 = getSymbolInternal(CONST_BITVECTOR, btn, "b1");
  Node bvc = getSymbolInternal(CONST_BITVECTOR, btnv, "bvc");
  for (size_t i = 0; i < w; i++)
  {
    Node arg = bv.isBitSet((w - 1) - i) ? b1 : b0;
    ret = mkApplyUf(bvc, {arg, ret});
  }
  return ret;
}

Node AlfNodeConverter::getNullTerminator(Kind k, TypeNode tn)
{
  NodeManager* nm = NodeManager::currentNM();
  Node tc = typeAsNode(convertType(tn));
  TypeNode ftype = nm->mkFunctionType({tc.getType()}, tn);
  Node nil = getSymbolInternal(k, ftype, "alf.nil");
  return mkApplyUf(nil, {tc});
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
