/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of ALF node conversion
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALF__ALF_NODE_CONVERTER_H
#define CVC4__PROOF__ALF__ALF_NODE_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/type_node.h"

namespace cvc5::internal {
namespace proof {

/**
 * This is a helper class for the ALF printer that converts nodes into
 * form that ALF expects. It should only be used by the ALF printer.
 */
class AlfNodeConverter : public NodeConverter
{
 public:
  AlfNodeConverter();
  ~AlfNodeConverter() {}
  /** convert at pre-order traversal */
  Node preConvert(Node n) override;
  /** convert at post-order traversal */
  Node postConvert(Node n) override;
  /**
   * Return the properly named operator for n of the form (f t1 ... tn), where
   * f could be interpreted or uninterpreted.  This method is used for cases
   * where it is important to get the term corresponding to the operator for
   * a term. An example is for the base REFL step of nested CONG.
   */
  Node getOperatorOfTerm(Node n);
  /**
   * Get the variable index for free variable fv, or assign a fresh index if it
   * is not yet assigned.
   */
  size_t getOrAssignIndexForConst(Node c);
  /** */
  Node mkNil(TypeNode tn);
  /**
   * Make an internal symbol with custom name. This is a BOUND_VARIABLE that
   * has a distinguished status so that it is *not* printed as (bvar ...). The
   * returned variable is always fresh.
   */
  Node mkInternalSymbol(const std::string& name,
                        TypeNode tn,
                        bool useRawSym = true);
  /**
   * Make an internal symbol with custom name. This is a BOUND_VARIABLE that
   * has a distinguished status so that it is *not* printed as (bvar ...). The
   * returned variable is always fresh.
   */
  Node mkInternalApp(const std::string& name,
                     const std::vector<Node>& args,
                     TypeNode ret,
                     bool useRawSym = true);
  /**
   * Type as node, returns a node that prints in the form that ALF will
   * interpret as the type tni. This method is required since types can be
   * passed as arguments to terms. This method assumes that tni has been
   * converted to internal form (via the convertType method of this class).
   */
  Node typeAsNode(TypeNode tni);

 private:
  /** Should we traverse n? */
  bool shouldTraverse(Node n) override;
  /**
   * Make APPLY_UF, which ensures the operator op is a variable. If it is not,
   * we create a dummy variable whose name is the result of printing op. This
   * is to ensure proper smt2 printing, which does not permit operators to
   * be higher-order terms.
   */
  Node mkApplyUf(Node op, const std::vector<Node>& args) const;
  /**
   * Make skolem function, if k was constructed by a skolem function identifier
   * (in SkolemManager::mkSkolemFunction) that is supported in the ALF
   * signature.
   */
  Node maybeMkSkolemFun(Node k);
  /** Is k a kind that is printed as an indexed operator in ALF? */
  static bool isIndexedOperatorKind(Kind k);
  /** get indices for printing the operator of n in the ALF format */
  static std::vector<Node> getOperatorIndices(Kind k, Node n);
  /** the set of all internally generated symbols */
  std::unordered_set<Node> d_symbols;
  /** the type of ALF sorts, which can appear in terms */
  TypeNode d_sortType;
  /** Used for getting unique index for free variable */
  std::map<Node, size_t> d_constIndex;
  /**
   */
  std::map<std::string, size_t> d_varIndex;
  /** Cache for typeAsNode */
  std::map<TypeNode, Node> d_typeAsNode;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
