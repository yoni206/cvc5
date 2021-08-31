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

void IntToBV::translateUF(Node uf,
                          vector<Node> children,
                          NodeMap& cache,
                          std::map<Node, vector<Node>>& ufToUFs,
                          uint64_t max)
{
  // nothing to do if already processed
  if (cache.find(uf) != cache.end() ) {
    return;
  }
  
  // obtain node and skolem managers
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();

  // obtain the types relevant to the original (Integer) UF
  TypeNode type = uf.getType();
  vector<TypeNode> originalArgTypes = type.getArgTypes();
  TypeNode originalRangeType = type.getRangeType();

  // declare types relevant to the translated (BV) UF
  vector<TypeNode> newArgTypes;
  TypeNode newRangeType;

  // compute the new types
  for (uint64_t i = 0, length = originalArgTypes.size(); i < length; i++)
  {
    TypeNode tn = originalArgTypes[i];
    // integer types are translated to BV types
    if (tn == nm->integerType())
    {
      // obtain argument type from the translated children
      TypeNode ctn = children[i].getType();
      Assert(ctn.isBitVector());
      newArgTypes.push_back(ctn);
    }
    else
    {
      // non-integer types remain intact
      newArgTypes.push_back(tn);
    }
  }
  // integer range types become BV rante types,
  // according to `max`.
  if (originalRangeType == nm->integerType())
  {
    newRangeType = nm->mkBitVectorType(max);
  }
  else
  {
    // non integer types remain intact.
    newRangeType = originalRangeType;
  }

  // a fresh function symbol with the new type
  Node result = sm->mkDummySkolem("__intToBV_uf",
                             nm->mkFunctionType(newArgTypes, newRangeType),
                             "Function symbol introduced in intToBV pass");
  
  // store new UF in cache
  cache[uf] = result;
  // add uf and its translation to the UF map
  if (ufToUFs.find(uf) == ufToUFs.end()) {
	  ufToUFs[uf] = {};
  }
  ufToUFs[uf].push_back(result);
}

void IntToBV::addSubstitution(Node uf, Node result, vector<TypeNode> originalArgTypes, vector<TypeNode> newArgTypes, TypeNode originalRangeType, TypeNode newRangeType) {
  NodeManager* nm = NodeManager::currentNM();
  vector<Node> args;
  vector<Node> achildren;
  achildren.push_back(result);
  for (uint64_t i=0, len = originalArgTypes.size(); i<len; i++) {
    TypeNode& d = originalArgTypes[i];
    Node freshBoundVar = nm->mkBoundVar(d);
    args.push_back(freshBoundVar);
    Node casted = freshBoundVar;
    if (d.isInteger())
    {
      Node intToBVOp = nm->mkConst<IntToBitVector>(newArgTypes[i].getBitVectorSize());
      casted = nm->mkNode(intToBVOp, casted);
    }
    achildren.push_back(casted);
  }
  Node app = nm->mkNode(kind::APPLY_UF, achildren);
  if (originalRangeType.isInteger())
  {
    app = nm->mkConst<IntToBitVector>(IntToBitVector(newRangeType.getBitVectorSize()));
  }
  Node lambda =
      nm->mkNode(kind::LAMBDA, nm->mkNode(kind::BOUND_VAR_LIST, args), app);
  d_preprocContext->addSubstitution(uf, lambda);
}

Node IntToBV::intToBV(TNode n, NodeMap& cache, std::map<Node, vector<Node>> ufs)
{
  // size of bit-vector variables and constants given by the user.
  int size = options::solveIntAsBV();
  AlwaysAssert(size > 0);
  // int-to-bv does not support incremental solving
  AlwaysAssert(!options::incrementalSolving());

  // get node and skolem managers
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();

  // binarize node
  NodeMap binaryCache;
  Node n_binary = intToBVMakeBinary(n, binaryCache);

  // traverse node and translate. Skip nodes already in the cache.
  for (TNode current : NodeDfsIterable(n_binary, VisitOrder::POSTORDER,
           [&cache](TNode nn) { return cache.count(nn) > 0; }))
  {
    Trace("int-to-bv-debug") << "current: " << current << std::endl;
    if (current.getNumChildren() > 0)
    {
      // Not a leaf. Children were already translated.
      // 
      // maximal bit-width observed within children, or needed
      // to prevent overflow. when `size` is smaller, the bit-vector will be padded
      // using signed extension.
      uint64_t max = 0;
      
      // compute the maximal size of the children.
      // store translated children in `children`
      vector<Node> children;
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

      // translate current according to its kind
      kind::Kind_t newKind = current.getKind();
      // bit-widths are at least 1
      Assert(max > 0);
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
      // build translated node
      NodeBuilder builder(newKind);
      // uninterpreted functions are treated in a special manner
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        Assert(current.getKind() == kind::APPLY_UF);
        Node uf = current.getOperator();
        translateUF(uf, children, cache, ufs, max);
        builder << cache[uf];
      }
      builder.append(children);
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
          /**
           * Correctly convert signed/unsigned BV values to Integers as follows
           * x < 0 ? -nat(-x) : nat(x)
           * where x refers to the bit-vector term `result`.
           */
          BitVector bvzero(size, Integer(0));
          Node negResult = nm->mkNode(kind::BITVECTOR_TO_NAT,
                                      nm->mkNode(kind::BITVECTOR_NEG, result));
          Node bv2int = nm->mkNode(
              kind::ITE,
              nm->mkNode(kind::BITVECTOR_SLT, result, nm->mkConst(bvzero)),
              nm->mkNode(kind::UMINUS, negResult),
              nm->mkNode(kind::BITVECTOR_TO_NAT, result));
          d_preprocContext->addSubstitution(current, bv2int);
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
    Trace("int-to-bv-debug")
        << "cache[current] " << cache[current] << std::endl;
  }
  Trace("int-to-bv-debug") << "original: " << n << std::endl;
  Trace("int-to-bv-debug") << "binary: " << n_binary << std::endl;
  Trace("int-to-bv-debug") << "result: " << cache[n_binary] << std::endl;
  NodeMap finalUFCache;
  unifyUFs(ufToUFs, finalUFCache);
  cache[n_binary] = updateUFs(cache[n_binary], finalUFCache, ufToUFs);
  return cache[n_binary];
}

void IntToBV::unifyUFs(map<Node, vector<Node> ufToUFs, NodeMap& finalUFCache) 
{
  for (pair<Node, vector<Node>> p : ufToUFs)
  {
    Node intUF = p.first;
    Node bvUFs = p.second;
    Assert(bvUFs.size() > 0);
    vector<TypeNode> finalArgTypes = bvUFs[0].getArgTypes();
    uint64_t numOfArgs = finalArgTypes.size();
    TypeNode finalRangeType = bvUFs[0].getRangeType();
    for (uint64_t i=1, len = bvUFs.size(); i++; i < len) {
      // initialize arguments bit-widths to numOfArgs zeros.
      Node bvUF = bvUFs[i];
      TypeNode type = bvUF.getType();
      vector<TypeNode> argTypes = type.getArgTypes();
      TypeNode rangeType = type.getRangeType();
      Assert(argTypes.size() == numOfArgs);
      for (uint64_t i=0; i < numOfArgs; i++) {
        if (argTypes[i].isBitVectorType() && finalArgTypes[i].getBitVectorSize() < argTypes[i].getBitVectorSize()) {
	  finalArgTypes[i] = argTypes[i];
	}
      }
      if (rangeType.isBitVectorType() && finalRangeType.getBitVectorSize() < rangeType.getBitVectorSize()) 
      {
        finalRangeType = type.getRangeType();
      }
      Node finalBVUF = sm->mkDummySkolem("__intToBV_uf",
                                 nm->mkFunctionType(newArgTypes, newRangeType),
                                 "Function symbol introduced in intToBV pass");
      finalUFCache[intUF] = finalBVUF;
      // a fresh function symbol with the new type
      addsubstitution(intUF, finalBVUF, originalArgTypes, newArgTypes, originalRangeType, newRangeType);
    }
  }
}
  
void IntToBV::updateUFs(Node n, const NodeMap& finalUFCache, const vector<Node, vector<Node>>& ufToUFs, NodeMap& cache);
{
  for (TNode current : NodeDfsIterable(n, VisitOrder::POSTORDER,
           [&cache](TNode nn) { return cache.count(nn) > 0; }))
  {
    
  }
  
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
