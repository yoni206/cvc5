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
#include "theory/builtin/generic_op.h"
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
    case PfRule::CONG: return true;
    default: return false;
  }
}

bool AlfProofPostprocessCallback::addAlfStep(AlfRule rule,
                                             Node conclusion,
                                             const std::vector<Node>& children,
                                             const std::vector<Node>& args,
                                             CDProof& cdp)
{
  std::vector<Node> newArgs;
  NodeManager * nm =NodeManager::currentNM();
  newArgs.push_back(nm->mkConstInt(Rational(static_cast<uint32_t>(rule))));
  newArgs.push_back(conclusion);
  for (const Node& arg : args)
  {
    newArgs.push_back(arg);
  }
  Trace("alethels-proof") << "... add alf step " << conclusion << " " << rule
                          << " " << children << " / " << newArgs << std::endl;
  return cdp.addStep(conclusion, PfRule::ALF_RULE, children, newArgs);
}

void AlfProofPostprocessCallback::addReflStep(const Node& n, CDProof& cdp)
{
  // share REFL
  std::map<Node, std::shared_ptr<ProofNode> >::iterator it = d_refl.find(n);
  if (it == d_refl.end())
  {
    d_refl[n] = d_pnm->mkNode(PfRule::REFL, {}, {n});
    it = d_refl.find(n);
  }
  cdp.addProof(it->second);
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

      Kind k = res[0].getKind();
      if (k == HO_APPLY)
      {
        // HO_APPLY congruence is a single application of HO_CONG
        cdp->addStep(res, PfRule::HO_CONG, children, {});
        return true;
      }
      // get the operator
      Node op = d_tproc.getOperatorOfTerm(res[0]);
      Trace("alf-proof") << "Processing cong for op " << op << " "
                         << op.getType() << std::endl;
      if (res[0].isClosure())
      {
        Assert (children.size()==2);
        // variable lists should be equal
        Assert (res[0][0]==res[1][0]);
        std::vector<Node> vars(res[0][0].begin(), res[0][0].end());
        // expects in reverse order
        std::reverse(vars.begin(), vars.end());
        Node vl = d_tproc.mkSExpr(vars);
        addAlfStep(AlfRule::CLOSURE_CONG, res, {children[1]}, {op, vl}, *cdp);
        return true;
      }
      /*
      if (GenericOp::isIndexedOperatorKind(k))
      {
        // if an indexed operator, we have to add refl steps for the indices
        std::vector<Node> ichildren;
        for (const Node& i : op)
        {
          addReflStep(i, *cdp);
          ichildren.push_back(i.eqNode(i));
        }
        ichildren.insert(ichildren.end(), children.begin(), children.end());
        // we are doing congruence on the operator
        op = op.getOperator();
        addAlfStep(AlfRule::CONG, res, ichildren, {op}, *cdp);
        return true;
      }
      */
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
        std::vector<Node> cargs;
        cargs.push_back(op);
        cargs.push_back(d_tproc.getNullTerminator(k, res[0].getType()));
        // use n-ary rule, must reverse children
        addAlfStep(AlfRule::NARY_CONG, res, rchildren, cargs, *cdp);
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
