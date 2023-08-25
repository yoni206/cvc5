/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The post processor for the experimental AletheLF format.
 */

#include "proof/alf/alf_post_processor.h"

#include <vector>

#include "proof/lazy_proof.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace proof {

AletheLFProofPostprocessCallback::AletheLFProofPostprocessCallback(
    ProofNodeManager* pnm, LfscNodeConverter& ltp)
    : d_pnm(pnm), d_pc(pnm->getChecker()), d_tproc(ltp)
{
}

AletheLFProofPostprocess::AletheLFProofPostprocess(Env& env,
                                                   LfscNodeConverter& ltp)
    : EnvObj(env),
      d_cb(new proof::AletheLFProofPostprocessCallback(
          env.getProofNodeManager(), ltp))
{
}

bool AletheLFProofPostprocessCallback::shouldUpdate(
    std::shared_ptr<ProofNode> pn,
    const std::vector<Node>& fa,
    bool& continueUpdate)
{
  switch (pn->getRule())
  {
    case PfRule::AND_INTRO:
    {
      return (pn->getChildren().size() > 2);
    }
    case PfRule::CHAIN_RESOLUTION: return true;
    case PfRule::CONG: return true;
    default: return false;
  }
}

bool AletheLFProofPostprocessCallback::addAletheLFStep(
    AletheLFRule rule,
    Node conclusion,
    const std::vector<Node>& children,
    const std::vector<Node>& args,
    CDProof& cdp)
{
  std::vector<Node> newArgs{NodeManager::currentNM()->mkConstInt(
      Rational(static_cast<uint32_t>(rule)))};
  for (const Node& arg : args)
  {
    newArgs.push_back(arg);
  }
  Trace("alethels-proof") << "... add alf step " << conclusion << " " << rule
                          << " " << children << " / " << newArgs << std::endl;
  return cdp.addStep(conclusion, PfRule::ALF_RULE, children, newArgs);
}

bool AletheLFProofPostprocessCallback::update(Node res,
                                              PfRule id,
                                              const std::vector<Node>& children,
                                              const std::vector<Node>& args,
                                              CDProof* cdp,
                                              bool& continueUpdate)
{
  Trace("alf-proof") << "...AletheLF pre-update " << res << " " << id << " "
                     << children << " / " << args << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  switch (id)
  {
    case PfRule::AND_INTRO:
    {
      // Split one AND_INTRO into multiple NARY_AND_INTRO (if necessary)
      // create and_intro for each child
      size_t n = children.size();
      Assert(n > 2);
      Node conj = nm->mkNode(AND, children[n - 2], children[n - 1]);
      // Create base AND_INTRO
      cdp->addStep(
          conj, PfRule::AND_INTRO, {children[n - 2], children[n - 1]}, {});
      for (size_t i = 3; i <= n; i++)
      {
        std::vector<Node> conjuncts = {children[n - i]};
        for (const Node& child : conj)
        {
          conjuncts.push_back(child);
        }
        Node nextConj = nm->mkNode(AND, conjuncts);
        addAletheLFStep(AletheLFRule::AND_INTRO_NARY,
                        nextConj,
                        {children[n - i], conj},
                        {},
                        *cdp);
        conj = nextConj;
      }
      return true;
    }
    break;
    case PfRule::CHAIN_RESOLUTION:
    {
      // create and_intro for each child
      // create big conjunction for args
      Assert(children.size() >= 2);
      Node conj = nm->mkNode(AND, children);
      Node argsList = nm->mkNode(AND, args);
      // This AND_INTRO will also be preprocessed to multiple AND_INTRO_NARY
      cdp->addStep(conj, PfRule::AND_INTRO, children, std::vector<Node>());
      return addAletheLFStep(
          AletheLFRule::CHAIN_RESOLUTION, res, {conj}, {argsList}, *cdp);
    }
    case PfRule::CONG:
    {
      Assert(res.getKind() == EQUAL);
      Assert(res[0].getOperator() == res[1].getOperator());
      Trace("alf-proof") << "Processing congruence for " << res << " "
                         << res[0].getKind() << std::endl;

      // These Asserts captures features not yet implemented
      Assert(!res[0].isClosure());

      Kind k = res[0].getKind();
      if (k == HO_APPLY)
      {
        // HO_APPLY congruence is a single application of AletheLF congruence
        addAletheLFStep(AletheLFRule::HO_CONG, res, children, {}, *cdp);
        return true;
      }

      // We are proving f(t1, ..., tn) = f(s1, ..., sn), nested.
      // First, get the operator, which will be used for printing the base
      // REFL step. Notice this may be for interpreted or uninterpreted
      // function symbols.
      // TODO: this comes from the lfsc converter
      Node op = d_tproc.getOperatorOfTerm(res[0]);
      Trace("alf-proof") << "Processing cong for op " << op << " "
                         << op.getType() << std::endl;
      Assert(!op.isNull());
      // initial base step is REFL
      Node opEq = op.eqNode(op);
      cdp->addStep(opEq, PfRule::REFL, {}, {op});
      size_t nchildren = children.size();
      // Are we doing congruence of an n-ary operator? If so, notice that op
      // is a binary operator and we must apply congruence in a special way.
      // Note we use the first block of code if we have more than 2 children.
      // special case: constructors and apply uf are not treated as n-ary; these
      // symbols have function types that expect n arguments.
      bool isNary = NodeManager::isNAryKind(k) && k != kind::APPLY_CONSTRUCTOR
                    && k != kind::APPLY_UF;

      // TODO: is this correct? this was taken from LFSC
      if (isNary && nchildren > 2)
      {
        Node currEq = children[nchildren - 1];
        for (size_t i = 0; i < nchildren; i++)
        {
          size_t ii = (nchildren - 1) - i;
          Trace("alf-proof") << "Process child " << ii << std::endl;
          Node uop = op;
          // special case: applications of the following kinds in the chain may
          // have a different type, so remake the operator here.
          if (k == kind::BITVECTOR_CONCAT || k == ADD || k == MULT
              || k == NONLINEAR_MULT)
          {
            // we get the operator of the next argument concatenated with the
            // current accumulated remainder.
            Node currApp = nm->mkNode(k, children[ii][0], currEq[0]);
            uop = d_tproc.getOperatorOfTerm(currApp);
          }
          Trace("alf-proof") << "Apply " << uop << " to " << children[ii][0]
                             << " and " << children[ii][1] << std::endl;
          Node argAppEq =
              nm->mkNode(HO_APPLY, uop, children[ii][0])
                  .eqNode(nm->mkNode(HO_APPLY, uop, children[ii][1]));
          addAletheLFStep(
              AletheLFRule::HO_CONG, argAppEq, {opEq, children[ii]}, {}, *cdp);
          // now, congruence to the current equality
          Node nextEq;
          if (ii == 0)
          {
            // use final conclusion
            nextEq = res;
          }
          else
          {
            // otherwise continue to apply
            nextEq = nm->mkNode(HO_APPLY, argAppEq[0], currEq[0])
                         .eqNode(nm->mkNode(HO_APPLY, argAppEq[1], currEq[1]));
          }
          // cdp, conclusion, children, rule, args
          addAletheLFStep(
              AletheLFRule::HO_CONG, nextEq, {argAppEq, currEq}, {}, *cdp);
          currEq = nextEq;
        }
      }
      else
      {
        updateCong(res, children, cdp, op);
      }
    }
    break;
    default: return false;
  }
  return true;
}

void AletheLFProofPostprocessCallback::updateCong(
    Node res, const std::vector<Node>& children, CDProof* cdp, Node startOp)
{
  Node currEq;
  size_t i = 0;
  size_t nchildren = children.size();
  if (!startOp.isNull())
  {
    // start with reflexive equality on operator
    currEq = startOp.eqNode(startOp);
  }
  else
  {
    // first child specifies (higher-order) operator equality
    currEq = children[0];
    i++;
  }
  Node curL = currEq[0];
  Node curR = currEq[1];
  NodeManager* nm = NodeManager::currentNM();
  for (; i < nchildren; i++)
  {
    // CONG rules for each child
    Node nextEq;
    if (i + 1 == nchildren)
    {
      // if we are at the end, we prove the final equality
      nextEq = res;
    }
    else
    {
      curL = nm->mkNode(HO_APPLY, curL, children[i][0]);
      curR = nm->mkNode(HO_APPLY, curR, children[i][1]);
      nextEq = curL.eqNode(curR);
    }
    // cdp, conclusion, children, rule, args
    addAletheLFStep(
        AletheLFRule::HO_CONG, nextEq, {currEq, children[i]}, {}, *cdp);
    currEq = nextEq;
  }
}

void AletheLFProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_env, *(d_cb.get()));
  updater.process(pf);
};

}  // namespace proof
}  // namespace cvc5::internal
