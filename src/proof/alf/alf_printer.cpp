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
 * The printer for the experimental Alf format.
 */

#include "proof/alf/alf_printer.h"

#include <cctype>
#include <iostream>
#include <memory>
#include <ostream>
#include <sstream>

#include "expr/node_algorithm.h"
#include "printer/printer.h"
#include "proof/alf/alf_proof_rule.h"
#include "proof/proof_node_to_sexpr.h"
#include "smt/print_benchmark.h"

namespace cvc5::internal {

namespace proof {

AlfPrinter::AlfPrinter(Env& env, AlfNodeConverter& atp, bool flatten)
    : EnvObj(env), d_tproc(atp), d_termLetPrefix("@t"), d_proofFlatten(flatten)
{
  d_pfType = NodeManager::currentNM()->mkSort("proofType");
}

bool AlfPrinter::isHandled(const ProofNode* pfn) const
{
  switch (pfn->getRule())
  {
    case PfRule::REFL:
    case PfRule::SYMM:
    case PfRule::TRANS:
    case PfRule::CONG:
    case PfRule::TRUE_INTRO:
    case PfRule::TRUE_ELIM:
    case PfRule::FALSE_INTRO:
    case PfRule::FALSE_ELIM:
    case PfRule::SPLIT:
    case PfRule::EQ_RESOLVE:
    case PfRule::MODUS_PONENS:
    case PfRule::NOT_NOT_ELIM:
    case PfRule::CONTRA:
    case PfRule::AND_ELIM:
    case PfRule::AND_INTRO:
    case PfRule::NOT_OR_ELIM:
    case PfRule::IMPLIES_ELIM:
    case PfRule::NOT_IMPLIES_ELIM1:
    case PfRule::NOT_IMPLIES_ELIM2:
    case PfRule::EQUIV_ELIM1:
    case PfRule::EQUIV_ELIM2:
    case PfRule::NOT_EQUIV_ELIM1:
    case PfRule::NOT_EQUIV_ELIM2:
    case PfRule::XOR_ELIM1:
    case PfRule::XOR_ELIM2:
    case PfRule::NOT_XOR_ELIM1:
    case PfRule::NOT_XOR_ELIM2:
    case PfRule::ITE_ELIM1:
    case PfRule::ITE_ELIM2:
    case PfRule::NOT_ITE_ELIM1:
    case PfRule::NOT_ITE_ELIM2:
    case PfRule::NOT_AND:
    case PfRule::CNF_AND_NEG:
    case PfRule::CNF_OR_POS:
    case PfRule::CNF_OR_NEG:
    case PfRule::CNF_IMPLIES_POS:
    case PfRule::CNF_IMPLIES_NEG1:
    case PfRule::CNF_IMPLIES_NEG2:
    case PfRule::CNF_EQUIV_POS1:
    case PfRule::CNF_EQUIV_POS2:
    case PfRule::CNF_EQUIV_NEG1:
    case PfRule::CNF_EQUIV_NEG2:
    case PfRule::CNF_XOR_POS1:
    case PfRule::CNF_XOR_POS2:
    case PfRule::CNF_XOR_NEG1:
    case PfRule::CNF_XOR_NEG2:
    case PfRule::CNF_ITE_POS1:
    case PfRule::CNF_ITE_POS2:
    case PfRule::CNF_ITE_POS3:
    case PfRule::CNF_ITE_NEG1:
    case PfRule::CNF_ITE_NEG2:
    case PfRule::CNF_ITE_NEG3:
    case PfRule::CNF_AND_POS:
    case PfRule::FACTORING:
    case PfRule::REORDERING:
    case PfRule::RESOLUTION:
    case PfRule::CHAIN_RESOLUTION:
    case PfRule::ALF_RULE: return true; break;
    //
    case PfRule::SUBS:
    case PfRule::REWRITE:
    case PfRule::EVALUATE:
    case PfRule::MACRO_SR_EQ_INTRO:
    case PfRule::MACRO_SR_PRED_INTRO:
    case PfRule::MACRO_SR_PRED_ELIM:
    case PfRule::MACRO_SR_PRED_TRANSFORM:
    case PfRule::ANNOTATION:
    case PfRule::DSL_REWRITE:
    case PfRule::REMOVE_TERM_FORMULA_AXIOM:
    case PfRule::THEORY_LEMMA:
    case PfRule::THEORY_REWRITE:
    case PfRule::PREPROCESS:
    case PfRule::PREPROCESS_LEMMA:
    case PfRule::THEORY_PREPROCESS:
    case PfRule::THEORY_PREPROCESS_LEMMA:
    case PfRule::THEORY_EXPAND_DEF:
    case PfRule::WITNESS_AXIOM:
    case PfRule::TRUST_REWRITE:
    case PfRule::TRUST_FLATTENING_REWRITE:
    case PfRule::TRUST_SUBS:
    case PfRule::TRUST_SUBS_MAP:
    case PfRule::TRUST_SUBS_EQ:
    case PfRule::THEORY_INFERENCE:
    case PfRule::SAT_REFUTATION:
    case PfRule::MACRO_RESOLUTION:
    case PfRule::MACRO_RESOLUTION_TRUST:
    case PfRule::HO_APP_ENCODE:
    case PfRule::HO_CONG:
    case PfRule::BETA_REDUCE:
    case PfRule::ARRAYS_READ_OVER_WRITE:
    case PfRule::ARRAYS_READ_OVER_WRITE_CONTRA:
    case PfRule::ARRAYS_READ_OVER_WRITE_1:
    case PfRule::ARRAYS_EXT:
    case PfRule::ARRAYS_EQ_RANGE_EXPAND:
    case PfRule::BV_BITBLAST:
    case PfRule::BV_BITBLAST_STEP:
    case PfRule::BV_EAGER_ATOM:
    case PfRule::DT_UNIF:
    case PfRule::DT_INST:
    case PfRule::DT_COLLAPSE:
    case PfRule::DT_SPLIT:
    case PfRule::DT_CLASH:
    case PfRule::SKOLEM_INTRO:
    case PfRule::SKOLEMIZE:
    case PfRule::INSTANTIATE:
    case PfRule::ALPHA_EQUIV:
    case PfRule::QUANTIFIERS_PREPROCESS:
    case PfRule::CONCAT_EQ:
    case PfRule::CONCAT_UNIFY:
    case PfRule::CONCAT_CONFLICT:
    case PfRule::CONCAT_SPLIT:
    case PfRule::CONCAT_CSPLIT:
    case PfRule::CONCAT_LPROP:
    case PfRule::CONCAT_CPROP:
    case PfRule::STRING_DECOMPOSE:
    case PfRule::STRING_LENGTH_POS:
    case PfRule::STRING_LENGTH_NON_EMPTY:
    case PfRule::STRING_REDUCTION:
    case PfRule::STRING_EAGER_REDUCTION:
    case PfRule::RE_INTER:
    case PfRule::RE_UNFOLD_POS:
    case PfRule::RE_UNFOLD_NEG:
    case PfRule::RE_UNFOLD_NEG_CONCAT_FIXED:
    case PfRule::RE_ELIM:
    case PfRule::STRING_CODE_INJ:
    case PfRule::STRING_SEQ_UNIT_INJ:
    case PfRule::STRING_INFERENCE:
    case PfRule::MACRO_ARITH_SCALE_SUM_UB:
    case PfRule::ARITH_SUM_UB:
    case PfRule::ARITH_TRICHOTOMY:
    case PfRule::INT_TIGHT_LB:
    case PfRule::INT_TIGHT_UB:
    case PfRule::ARITH_MULT_SIGN:
    case PfRule::ARITH_MULT_POS:
    case PfRule::ARITH_MULT_NEG:
    case PfRule::ARITH_MULT_TANGENT:
    case PfRule::ARITH_OP_ELIM_AXIOM:
    case PfRule::ARITH_POLY_NORM:
    case PfRule::ARITH_TRANS_PI:
    case PfRule::ARITH_TRANS_EXP_NEG:
    case PfRule::ARITH_TRANS_EXP_POSITIVITY:
    case PfRule::ARITH_TRANS_EXP_SUPER_LIN:
    case PfRule::ARITH_TRANS_EXP_ZERO:
    case PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_NEG:
    case PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_POS:
    case PfRule::ARITH_TRANS_EXP_APPROX_BELOW:
    case PfRule::ARITH_TRANS_SINE_BOUNDS:
    case PfRule::ARITH_TRANS_SINE_SHIFT:
    case PfRule::ARITH_TRANS_SINE_SYMMETRY:
    case PfRule::ARITH_TRANS_SINE_TANGENT_ZERO:
    case PfRule::ARITH_TRANS_SINE_TANGENT_PI:
    case PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_NEG:
    case PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_POS:
    case PfRule::ARITH_TRANS_SINE_APPROX_BELOW_NEG:
    case PfRule::ARITH_TRANS_SINE_APPROX_BELOW_POS:
    case PfRule::ARITH_NL_COVERING_DIRECT:
    case PfRule::ARITH_NL_COVERING_RECURSIVE:
    default: break;
  }
  return false;
}

std::string AlfPrinter::getRuleName(const ProofNode* pfn)
{
  std::string name;
  if (pfn->getRule() == PfRule::ALF_RULE)
  {
    name = AlfRuleToString(getAlfRule(pfn->getArguments()[0]));
  }
  else
  {
    name = toString(pfn->getRule());
  }
  std::transform(name.begin(), name.end(), name.begin(), [](unsigned char c) {
    return std::tolower(c);
  });
  return name;
}

void AlfPrinter::printLetList(std::ostream& out, LetBinding& lbind)
{
  std::vector<Node> letList;
  lbind.letify(letList);
  std::map<Node, size_t>::const_iterator it;
  Printer* p = Printer::getPrinter(out);
  for (size_t i = 0, nlets = letList.size(); i < nlets; i++)
  {
    Node n = letList[i];
    Node def = lbind.convert(n, d_termLetPrefix, false);
    Node f = lbind.convert(n, d_termLetPrefix, true);
    p->toStreamCmdDefineFunction(out, f, def);
  }
}

void AlfPrinter::print(std::ostream& out, std::shared_ptr<ProofNode> pfn)
{
  d_pfIdCounter = 0;

  // [1] Get the definitions and assertions and print the declarations from them
  const std::vector<Node>& definitions = pfn->getArguments();
  const std::vector<Node>& assertions = pfn->getChildren()[0]->getArguments();
  const ProofNode* pnBody = pfn->getChildren()[0]->getChildren()[0].get();

  // TODO: preprocess definitions/assertions with the term converter
  // if the names change
  smt::PrintBenchmark pb(Printer::getPrinter(out));
  pb.printDeclarationsFrom(out, definitions, assertions);

  LetBinding lbind;
  AlfPrintChannelPre aletify(lbind);
  AlfPrintChannelOut aprint(out, lbind, d_termLetPrefix);

  d_pletMap.clear();
  d_passumeMap.clear();

  bool wasAlloc;
  for (size_t i = 0; i < 2; i++)
  {
    AlfPrintChannel* aout;
    if (i == 0)
    {
      aout = &aletify;
    }
    else
    {
      aout = &aprint;
    }
    if (i == 1)
    {
      // [2] print proof-level term bindings
      printLetList(out, lbind);
    }
    // [3] print assumptions
    for (const Node& n : definitions)
    {
      // TODO: not exactly necessary, could be refl
      size_t id = allocateAssumeId(n, wasAlloc);
      aout->printAssume(n, id, false);
    }
    for (const Node& n : assertions)
    {
      size_t id = allocateAssumeId(n, wasAlloc);
      aout->printAssume(n, id, false);
    }
    // [4] print proof body
    printProofInternal(aout, pnBody);
  }
  // if flattened, print the full proof as ident
  if (!d_proofFlatten)
  {
    d_pfIdCounter++;
    std::map<const ProofNode*, Node>::iterator it = d_pnodeMap.find(pnBody);
    if (it!=d_pnodeMap.end())
    {
      std::vector<Node> premises;
      aprint.printStep("identity", pnBody->getResult(), d_pfIdCounter, {it->second}, {});
    }
  }
}

void AlfPrinter::printProofInternal(AlfPrintChannel* out, const ProofNode* pn)
{
  // the stack
  std::vector<const ProofNode*> visit;
  // whether we have to process children
  std::unordered_map<const ProofNode*, bool> processingChildren;
  // helper iterators
  std::unordered_map<const ProofNode*, bool>::iterator pit;
  const ProofNode* cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    pit = processingChildren.find(cur);
    if (pit == processingChildren.end())
    {
      PfRule r = cur->getRule();
      if (r == PfRule::ASSUME)
      {
        // ignore
        visit.pop_back();
        continue;
      }
      else if (r == PfRule::ENCODE_PRED_TRANSFORM)
      {
        // just add child
        visit.pop_back();
        visit.push_back(cur->getChildren()[0].get());
        continue;
      }
      printStepPre(out, cur);
      // a normal rule application, compute the proof arguments, which
      // notice in the case of PI also may modify our passumeMap.
      processingChildren[cur] = true;
      // will revisit this proof node
      const std::vector<std::shared_ptr<ProofNode>>& children =
          cur->getChildren();
      // visit each child
      for (const std::shared_ptr<ProofNode>& c : children)
      {
        visit.push_back(c.get());
      }
      continue;
    }
    visit.pop_back();
    if (pit->second)
    {
      processingChildren[cur] = false;
      printStepPost(out, cur);
    }
  } while (!visit.empty());
}

void AlfPrinter::printStepPre(AlfPrintChannel* out, const ProofNode* pn)
{
  // if we haven't yet allocated a proof id, do it now
  PfRule r = pn->getRule();
  if (r == PfRule::ALF_RULE)
  {
    Assert(!pn->getArguments().empty());
    Node rn = pn->getArguments()[0];
    AlfRule ar = getAlfRule(rn);
    if (ar == AlfRule::SCOPE)
    {
      Assert(pn->getArguments().size() == 2);
      Node a = pn->getArguments()[1];
      bool wasAlloc = false;
      size_t aid = allocateAssumeId(a, wasAlloc);
      // if we assigned an id to the assumption,
      if (wasAlloc)
      {
        d_activeScopes.insert(pn);
      }
      else
      {
        // otherwise we shadow, just use a dummy
        d_pfIdCounter++;
        aid = d_pfIdCounter;
      }
      // print a push
      out->printAssume(a, aid, true);
    }
  }
}
void AlfPrinter::printStepPost(AlfPrintChannel* out, const ProofNode* pn)
{
  // if we have yet to allocate a proof id, do it now
  bool wasAlloc = false;
  bool isPop = false;
  TNode conclusion = pn->getResult();
  TNode conclusionPrint;
  // print conclusion only if option is set
  if (options().proof.proofPrintConclusion)
  {
    conclusionPrint = conclusion;
  }
  PfRule r = pn->getRule();
  std::vector<Node> args;
  const std::vector<Node> aargs = pn->getArguments();
  if (r == PfRule::ALF_RULE)
  {
    Node rn = aargs[0];
    AlfRule ar = getAlfRule(rn);
    // if scope, do pop the assumption from passumeMap
    if (ar == AlfRule::SCOPE)
    {
      isPop = true;
      // FIXME
      if (d_activeScopes.find(pn) != d_activeScopes.end())
      {
        Node a = aargs[1];
        d_passumeMap.erase(a);
      }
      // note that aargs[1] is not provided, it is consumed as an assumption
    }
    else
    {
      args.insert(args.end(), aargs.begin() + 1, aargs.end());
    }
  }
  else
  {
    ProofNodeToSExpr pntse;
    for (size_t i = 0, nargs = aargs.size(); i < nargs; i++)
    {
      ProofNodeToSExpr::ArgFormat f = pntse.getArgumentFormat(pn, i);
      Node av = pntse.getArgument(aargs[i], f);
      args.push_back(av);
    }
  }
  const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();
  // if not flattening proofs
  if (!d_proofFlatten)
  {
    std::vector<Node> pargs;
    std::string rname;
    if (!isHandled(pn))
    {
      rname = "trust";
      pargs.push_back(conclusion);
    }
    else
    {  
      rname = getRuleName(pn);
      std::map<Node, size_t>::iterator ita;
      std::map<const ProofNode*, Node>::iterator itp;
      for (const std::shared_ptr<ProofNode>& c : children)
      {
        Node arg;
        if (c->getRule() == PfRule::ASSUME)
        {
          ita = d_passumeMap.find(c->getResult());
          Assert(ita != d_passumeMap.end());
          arg = allocatePremise(ita->second);
        }
        else
        {
          itp = d_pnodeMap.find(c.get());
          Assert(itp != d_pnodeMap.end());
          arg = itp->second;
        }
        pargs.push_back(arg);
      }
      if (isPop)
      {
        // we must manually print pops
        size_t id = allocateProofId(pn, wasAlloc);
        out->printStep(rname, conclusionPrint, id, pargs, args, isPop);
        if (d_pnodeMap.find(pn)==d_pnodeMap.end())
        {
          d_pnodeMap[pn] = allocatePremise(id);
        }
        return;
      }
      pargs.insert(pargs.end(), args.begin(), args.end());
    }
    // otherwise just make the node
    if (d_pnodeMap.find(pn)==d_pnodeMap.end())
    {
      d_pnodeMap[pn] = d_tproc.mkInternalApp(rname, pargs, d_pfType);
    }
    return;
  }
  size_t id = allocateProofId(pn, wasAlloc);
  // if we don't handle the rule, print trust
  if (!isHandled(pn))
  {
    out->printTrust(pn->getRule(), conclusionPrint, id, conclusion);
    return;
  }
  std::vector<Node> premises;
  // get the premises
  std::map<Node, size_t>::iterator ita;
  std::map<const ProofNode*, size_t>::iterator itp;
  for (const std::shared_ptr<ProofNode>& c : children)
  {
    size_t pid;
    // if assume, lookup in passumeMap
    if (c->getRule() == PfRule::ASSUME)
    {
      ita = d_passumeMap.find(c->getResult());
      Assert(ita != d_passumeMap.end());
      pid = ita->second;
    }
    else
    {
      itp = d_pletMap.find(c.get());
      Assert(itp != d_pletMap.end());
      pid = itp->second;
    }
    premises.push_back(allocatePremise(pid));
  }
  std::string rname = getRuleName(pn);
  out->printStep(rname, conclusionPrint, id, premises, args, isPop);
}

size_t AlfPrinter::allocateAssumeId(const Node& n, bool& wasAlloc)
{
  std::map<Node, size_t>::iterator it = d_passumeMap.find(n);
  if (it != d_passumeMap.end())
  {
    wasAlloc = false;
    return it->second;
  }
  wasAlloc = true;
  d_pfIdCounter++;
  d_passumeMap[n] = d_pfIdCounter;
  return d_pfIdCounter;
}

size_t AlfPrinter::allocateProofId(const ProofNode* pn, bool& wasAlloc)
{
  std::map<const ProofNode*, size_t>::iterator it = d_pletMap.find(pn);
  if (it != d_pletMap.end())
  {
    wasAlloc = false;
    return it->second;
  }
  wasAlloc = true;
  d_pfIdCounter++;
  d_pletMap[pn] = d_pfIdCounter;
  return d_pfIdCounter;
}

Node AlfPrinter::allocatePremise(size_t id)
{
  std::map<size_t, Node>::iterator itan = d_passumeNodeMap.find(id);
  if (itan!=d_passumeNodeMap.end())
  {
    return itan->second;
  }
  std::stringstream ss;
  ss << "@p" << id;
  Node n = d_tproc.mkInternalSymbol(ss.str(), d_pfType);
  d_passumeNodeMap[id] = n;
  return n;
}

}  // namespace proof
}  // namespace cvc5::internal