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
 * The post processor for the experimental Alf format.
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

AlfProofPostprocessCallback::AlfProofPostprocessCallback(ProofNodeManager* pnm,
                                                         AlfNodeConverter& ltp)
    : d_pnm(pnm), d_pc(pnm->getChecker()), d_tproc(ltp), d_numIgnoredScopes(0)
{
}

AlfProofPostprocess::AlfProofPostprocess(Env& env, AlfNodeConverter& ltp)
    : EnvObj(env),
      d_cb(new proof::AlfProofPostprocessCallback(env.getProofNodeManager(),
                                                  ltp))
{
}

bool AlfProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                               const std::vector<Node>& fa,
                                               bool& continueUpdate)
{
  switch (pn->getRule())
  {
    case PfRule::SCOPE:
    case PfRule::CONG:return true;
    default: return false;
  }
}

bool AlfProofPostprocessCallback::addAlfStep(AlfRule rule,
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

bool AlfProofPostprocessCallback::update(Node res,
                                         PfRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args,
                                         CDProof* cdp,
                                         bool& continueUpdate)
{
  Trace("alf-proof") << "...Alf pre-update " << res << " " << id << " "
                     << children << " / " << args << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  switch (id)
  {
    case PfRule::SCOPE:
    {
      // On the first two calls to update, the proof node is the outermost
      // scopes of the proof. These scopes should not be printed in the LFSC
      // proof. Instead, the LFSC proof printer will print the proper scopes
      // around the proof, which e.g. involves an LFSC "check" command.
      if (d_numIgnoredScopes < 2)
      {
        d_numIgnoredScopes++;
        // Note that we do not want to modify the top-most SCOPEs.
        return false;
      }
      Node curr = children[0];
      for (size_t i = 0, nargs = args.size(); i < nargs; i++)
      {
        size_t ii = (nargs - 1) - i;
        Node next = nm->mkNode(IMPLIES, args[ii], curr);
        addAlfStep(AlfRule::SCOPE, next, {curr}, {args[ii]}, *cdp);
        curr = next;
      }
      // convert (=> F1 (=> ... (=> Fn C)...)) to (=> (and F1 ... Fn) C) or
      // (not (and F1 ... Fn))
      addAlfStep(AlfRule::PROCESS_SCOPE, res, {curr}, {children[0]}, *cdp);
    }
    break;
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
        // HO_APPLY congruence is a single application of HO_CONG
        cdp->addStep(res, PfRule::HO_CONG, children, {});
        return true;
      }

      // We are proving f(t1, ..., tn) = f(s1, ..., sn), nested.
      // First, get the operator, which will be used for printing the base
      // REFL step. Notice this may be for interpreted or uninterpreted
      // function symbols.
      Node op = d_tproc.getOperatorOfTerm(res[0]);
      Trace("alf-proof") << "Processing cong for op " << op << " "
                         << op.getType() << std::endl;
      Assert(!op.isNull());
      // Are we doing congruence of an n-ary operator? If so, notice that op
      // is a binary operator and we must apply congruence in a special way.
      // Note we use the first block of code if we have more than 2 children.
      // special case: constructors and apply uf are not treated as n-ary; these
      // symbols have function types that expect n arguments.
      bool isNary = NodeManager::isNAryKind(k) && k != kind::APPLY_CONSTRUCTOR
                    && k != kind::APPLY_UF;
      if (isNary)
      {
        std::vector<Node> rchildren = children;
        std::reverse(rchildren.begin(), rchildren.end());
        // use n-ary rule, must reverse children
        addAlfStep(AlfRule::NARY_CONG, res, rchildren, {op}, *cdp);
      }
      else
      {
        // use ordinary rule
        addAlfStep(AlfRule::CONG, res, children, {op}, *cdp);
      }
    }
    break;
    default: return false;
  }
  return true;
}

void AlfProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  ProofNodeUpdater updater(d_env, *(d_cb.get()));
  updater.process(pf);
};

}  // namespace proof
}  // namespace cvc5::internal
