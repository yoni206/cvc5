/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Yoni Zohar, Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The IntToBV preprocessing pass.
 *
 * Converts integer operations into bitvector operations. The width of the
 * bitvectors is controlled through the `--solve-int-as-bv` command line
 * option.
 */

#include "preprocessing/passes/int_to_bv.h"

#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "util/bitvector.h"
#include "util/rational.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::theory;


namespace {

bool childrenTypesChanged(Node n, NodeMap& cache) {
  for (Node child : n) {
    TypeNode originalType = child.getType();
    TypeNode newType = cache[child].getType();
    if (! newType.isSubtypeOf(originalType)) {
      return true;
    }
  }
  return false;
}


Node intToBVMakeBinary(TNode n, NodeMap& cache)
{
  for (TNode current : NodeDfsIterable(n, VisitOrder::POSTORDER,
           [&cache](TNode nn) { return cache.count(nn) > 0; }))
  {
    Node result;
    NodeManager* nm = NodeManager::currentNM();
    if (current.getNumChildren() == 0)
    {
      result = current;
    }
    else if (current.getNumChildren() > 2
             && (current.getKind() == kind::PLUS
                 || current.getKind() == kind::MULT
                 || current.getKind() == kind::NONLINEAR_MULT))
    {
      Assert(cache.find(current[0]) != cache.end());
      result = cache[current[0]];
      for (unsigned i = 1; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        Node child = current[i];
        Node childRes = cache[current[i]];
        result = nm->mkNode(current.getKind(), result, childRes);
      }
    }
    else
    {
      NodeBuilder builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << current.getOperator();
      }

      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        builder << cache[current[i]];
      }
      result = builder;
    }
    cache[current] = result;
  }
  return cache[n];
}
}  // namespace

Node IntToBV::intToBV(TNode n, NodeMap& cache)
{
  // size of bit-vector variables and constants given by the user.
  int size = options::solveIntAsBV();
  AlwaysAssert(size > 0);
  AlwaysAssert(!options::incrementalSolving());

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();

  // binarize node
  NodeMap binaryCache;
  Node n_binary = intToBVMakeBinary(n, binaryCache);

  // traverse node and translate. Skip nodes already in the cache.
  for (TNode current : NodeDfsIterable(n_binary, VisitOrder::POSTORDER,
           [&cache](TNode nn) { return cache.count(nn) > 0; }))
  {
    if (current.getNumChildren() > 0)
    {
      // Not a leaf
      // translated children of current
      vector<Node> children;
      // 
      // maximal bit-width observed within children, or needed
      // to prevent overflow. when `size` is smaller, the bit-vector will be padded
      // using signed extension.
      uint64_t max = 0;
      
      // compute the maximal size of the children, and store
      // stranslated children in `children`.
      for (const Node& nc : current)
      {
        Assert(cache.find(nc) != cache.end());
        TNode childRes = cache[nc];
        TypeNode type = childRes.getType();
        if (type.isBitVector())
        {
          uint32_t bvsize = type.getBitVectorSize();
          if (bvsize > max)
          {
            max = bvsize;
          }
        }
        children.push_back(childRes);
      }

      kind::Kind_t newKind = current.getKind();
      if (max > 0)
      {
	// determine the translated operation
        switch (newKind)
        {
          case kind::PLUS:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_ADD;
            max = max + 1;
            break;
          case kind::MULT:
          case kind::NONLINEAR_MULT:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_MULT;
            max = max * 2;
            break;
          case kind::MINUS:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_SUB;
            max = max + 1;
            break;
          case kind::UMINUS:
            Assert(children.size() == 1);
            newKind = kind::BITVECTOR_NEG;
            max = max + 1;
            break;
          case kind::LT: newKind = kind::BITVECTOR_SLT; break;
          case kind::LEQ: newKind = kind::BITVECTOR_SLE; break;
          case kind::GT: newKind = kind::BITVECTOR_SGT; break;
          case kind::GEQ: newKind = kind::BITVECTOR_SGE; break;
          case kind::EQUAL:
          case kind::APPLY_UF:
          case kind::ITE: break;
          default:
            if (childrenTypesChanged(current, cache)) {
              throw TypeCheckingExceptionPrivate(
                  current,
                  string("Cannot translate to BV: ") + current.toString());
            }
            break;
        }

	// pad children with sign extension according to max
        for (size_t i = 0, csize = children.size(); i < csize; ++i)
        {
          TypeNode type = children[i].getType();
          if (!type.isBitVector())
          {
            continue;
          }
          uint32_t bvsize = type.getBitVectorSize();
          if (bvsize < max)
          {
            // sign extend
            Node signExtendOp = nm->mkConst<BitVectorSignExtend>(
                BitVectorSignExtend(max - bvsize));
            children[i] = nm->mkNode(signExtendOp, children[i]);
          }
        }
      }
      NodeBuilder builder(newKind);
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << current.getOperator();
      }
      builder.append(children);
      // Mark the substitution and continue
      Node result = builder;

      result = Rewriter::rewrite(result);
      cache[current] = result;
    }
    else
    {
      // It's a leaf: could be a variable or a numeral
      Node result = current;
      if (current.isVar())
      {
	TypeNode type = current.getType();
        if (type == nm->integerType())
        {
          result = sm->mkDummySkolem("__intToBV_var",
                                     nm->mkBitVectorType(size),
                                     "Variable introduced in intToBV pass");
          Node bv2nat = nm->mkNode(kind::BITVECTOR_TO_NAT, result);
          d_preprocContext->addSubstitution(current, bv2nat);
        } else if (type.isFunction()) {
	    std::vector<TypeNode> originalArgTypes = type.getArgTypes();
	    TypeNode originalRangeType = type.getRangeType();
	    std::vector<TypeNode> newArgTypes;
	    TypeNode newRangeType;
	    for (TypeNode tn : originalArgTypes) {
		if (tn == nm->integerType()) {
			newArgTypes.push_back(nm->mkBitVectorType(size));
		} else {
			newArgTypes.push_back(tn);
		}
	    }
	    if (originalRangeType == nm->integerType()) {
		    newRangeType = nm->mkBitVectorType(size);
	    } else {
		      newRangeType = originalRangeType;
	    }
	    result = sm->mkDummySkolem("__intToBV_uf",
			    nm->mkFunctionType(newArgTypes, newRangeType),
			    "Function symbol introduced in intToBV pass");
	    vector<Node> args;
	    vector<Node> achildren;
	    achildren.push_back(result);
	    for (const TypeNode& d : originalArgTypes) {
		    Node freshBoundVar = nm->mkBoundVar(d);
		    args.push_back(freshBoundVar);
		    Node casted = freshBoundVar;
		    if (d.isInteger()) {
    			Node intToBVOp = nm->mkConst<IntToBitVector>(IntToBitVector(size));
			casted = nm->mkNode(intToBVOp, casted);
		    }
		    achildren.push_back(casted);	
	    }
	    Node app = nm->mkNode(kind::APPLY_UF, achildren);
	    if (originalRangeType.isInteger()) {
		app = nm->mkConst<IntToBitVector>(IntToBitVector(size));
	    }
	    Node lambda = nm->mkNode(kind::LAMBDA, nm->mkNode(kind::BOUND_VAR_LIST, args), app);
	    d_preprocContext->addSubstitution(current, lambda);
	}
      }
      else if (current.isConst())
      {
        switch (current.getKind())
        {
          case kind::CONST_RATIONAL:
          {
            Rational constant = current.getConst<Rational>();
            if (constant.isIntegral()) {
              BitVector bv(size, constant.getNumerator());
              if (bv.toSignedInteger() != constant.getNumerator())
              {
                throw TypeCheckingExceptionPrivate(
                    current,
                    string("Not enough bits for constant in intToBV: ")
                        + current.toString());
              }
              result = nm->mkConst(bv);
            }
            break;
          }
          default: break;
        }
      }
      else
      {
        throw TypeCheckingExceptionPrivate(
            current, string("Cannot translate to BV: ") + current.toString());
      }
      cache[current] = result;
    }
  }
  Trace("int-to-bv-debug") << "original: " << n << std::endl;
  Trace("int-to-bv-debug") << "binary: " << n_binary << std::endl;
  Trace("int-to-bv-debug") << "result: " << cache[n_binary] << std::endl;
  return cache[n_binary];
}

IntToBV::IntToBV(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "int-to-bv"){};

PreprocessingPassResult IntToBV::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeMap cache;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, intToBV((*assertionsToPreprocess)[i], cache));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
