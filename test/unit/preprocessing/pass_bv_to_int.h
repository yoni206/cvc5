/*********************                                                        */
/*! \file pass_bv_to_int.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for bv-to-int
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "preprocessing/passes/bv_to_int.h"
#include "preprocessing/preprocessing_pass_registry.h"
#include "smt/preprocessor.h"
#include "smt/process_assertions.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "test_utils.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/rewriter.h"

using namespace CVC4;
using namespace CVC4::preprocessing;
using namespace CVC4::preprocessing::passes;
using namespace CVC4::theory;
using namespace CVC4::theory::booleans;
using namespace CVC4::smt;

class BVToIntWhite : public CxxTest::TestSuite
{
 public:
  BVToIntWhite() {}

  void setUp() override
  {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_nm);
    d_scope = new SmtScope(d_smt);
    d_smt->finishInit();
    d_cp = new CircuitPropagator();
    d_pnm = new ProofNodeManager();
    d_ppc = new PreprocessingPassContext(d_smt, d_cp, d_pnm);
    d_ppr = &PreprocessingPassRegistry::getInstance();
    d_bvToIntPP = static_cast<BVToInt*>(
        d_smt->d_pp->d_processor.d_passes["bv-to-int"].get());
  }

  void tearDown() override
  {
    (void)d_scope;
    delete d_cp;
    delete d_pnm;
    delete d_ppc;
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void testSimplify()
  {
    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(4));
    Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(4));
    Node z = d_nm->mkVar("z", d_nm->mkBitVectorType(4));
    Node x_bvand_y = d_nm->mkNode(kind::BITVECTOR_AND, x, y);
    Node bv_eq = d_nm->mkNode(kind::EQUAL, x_bvand_y, z);
    std::unordered_map<Node, Node, NodeHashFunction> map;
    Node int_eq = d_bvToIntPP->getOneTimeTranslation(bv_eq, map);
  }

 private:
  ExprManager* d_em;
  NodeManager* d_nm;
  SmtEngine* d_smt;
  SmtScope* d_scope;
  CircuitPropagator* d_cp;
  ProofNodeManager* d_pnm;
  PreprocessingPassContext* d_ppc;
  PreprocessingPassRegistry* d_ppr;
  BVToInt* d_bvToIntPP;
};
