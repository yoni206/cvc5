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
#include "options/main_options.h"
#include "printer/printer.h"
#include "proof/alf/alf_proof_rule.h"
#include "proof/proof_node_to_sexpr.h"
#include "smt/print_benchmark.h"
#include "theory/strings/theory_strings_utils.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

namespace proof {

AlfPrinter::AlfPrinter(Env& env, AlfNodeConverter& atp, bool flatten)
    : EnvObj(env), d_tproc(atp), d_termLetPrefix("@t"), d_proofFlatten(flatten)
{
  d_pfType = NodeManager::currentNM()->mkSort("proofType");
  d_false = NodeManager::currentNM()->mkConst(false);
}

bool AlfPrinter::isHandled(const ProofNode* pfn) const
{
  const std::vector<Node> pargs = pfn->getArguments();
  switch (pfn->getRule())
  {
    case PfRule::REFL:
    case PfRule::SYMM:
    case PfRule::TRANS:
    case PfRule::CONG:
    case PfRule::HO_CONG:
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
    case PfRule::ARRAYS_READ_OVER_WRITE:
    case PfRule::ARRAYS_READ_OVER_WRITE_CONTRA:
    case PfRule::ARRAYS_READ_OVER_WRITE_1:
    case PfRule::ARRAYS_EXT:
    case PfRule::ARITH_SUM_UB:
    case PfRule::ARITH_MULT_POS:
    case PfRule::ARITH_MULT_NEG:
    case PfRule::ARITH_TRICHOTOMY:
    case PfRule::INT_TIGHT_LB:
    case PfRule::INT_TIGHT_UB:
    case PfRule::SKOLEM_INTRO:
    case PfRule::CONCAT_EQ:
    case PfRule::CONCAT_UNIFY:
    case PfRule::CONCAT_CSPLIT:
    case PfRule::CONCAT_CONFLICT:
    case PfRule::STRING_LENGTH_POS:
    case PfRule::STRING_LENGTH_NON_EMPTY:
    case PfRule::RE_INTER:
    case PfRule::RE_UNFOLD_POS:
    case PfRule::REMOVE_TERM_FORMULA_AXIOM:
    case PfRule::INSTANTIATE:
    case PfRule::SKOLEMIZE:
    case PfRule::DRAT_REFUTATION: return true;
    // alf rule is handled
    case PfRule::ALF_RULE: return true;
    case PfRule::STRING_REDUCTION:
    {
      // depends on the operator
      Assert(!pargs.empty());
      Kind k = pargs[0].getKind();
      return k == STRING_SUBSTR || k == STRING_INDEXOF;
    }
    break;
    case PfRule::STRING_EAGER_REDUCTION:
    {
      // depends on the operator
      Assert(!pargs.empty());
      Kind k = pargs[0].getKind();
      return k == STRING_CONTAINS || k == STRING_TO_CODE || k == STRING_INDEXOF;
    }
    break;
    //
    case PfRule::EVALUATE:
    {
      if (canEvaluate(pargs[0]))
      {
        Trace("alf-printer-debug") << "Can evaluate " << pargs[0] << std::endl;
        return true;
      }
    }
    break;
    case PfRule::ANNOTATION:
    case PfRule::DSL_REWRITE:
    case PfRule::THEORY_EXPAND_DEF:
    case PfRule::WITNESS_AXIOM:
    case PfRule::HO_APP_ENCODE:
    case PfRule::BETA_REDUCE:
    case PfRule::ARRAYS_EQ_RANGE_EXPAND:
    case PfRule::BV_BITBLAST:
    case PfRule::BV_BITBLAST_STEP:
    case PfRule::BV_EAGER_ATOM:
    case PfRule::DT_UNIF:
    case PfRule::DT_INST:
    case PfRule::DT_COLLAPSE:
    case PfRule::DT_SPLIT:
    case PfRule::DT_CLASH:
    case PfRule::ALPHA_EQUIV:
    case PfRule::QUANTIFIERS_PREPROCESS:
    case PfRule::CONCAT_SPLIT:
    case PfRule::CONCAT_LPROP:
    case PfRule::CONCAT_CPROP:
    case PfRule::STRING_DECOMPOSE:
    case PfRule::RE_UNFOLD_NEG:
    case PfRule::RE_UNFOLD_NEG_CONCAT_FIXED:
    case PfRule::RE_ELIM:
    case PfRule::STRING_CODE_INJ:
    case PfRule::STRING_SEQ_UNIT_INJ:
    case PfRule::ARITH_MULT_SIGN:
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

bool AlfPrinter::canEvaluate(Node n) const
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      switch (cur.getKind())
      {
        case CONST_INTEGER:
        case CONST_RATIONAL:
        case CONST_STRING:
        case ADD:
        case SUB:
        case NEG:
        case EQUAL:
        case LT:
        case GT:
        case GEQ:
        case LEQ:
        case MULT:
        case NONLINEAR_MULT:
        case STRING_CONCAT:
        case STRING_SUBSTR:
        case STRING_LENGTH:
        case BITVECTOR_ADD:
        case BITVECTOR_SUB:
        case BITVECTOR_NEG: break;
        default:
          Trace("alf-printer-debug")
              << "Cannot evaluate " << cur.getKind() << std::endl;
          return false;
      }
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
  return true;
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

  // Get the definitions and assertions and print the declarations from them
  const std::vector<Node>& definitions = pfn->getArguments();
  const std::vector<Node>& assertions = pfn->getChildren()[0]->getArguments();
  const ProofNode* pnBody = pfn->getChildren()[0]->getChildren()[0].get();

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
      std::stringstream outVars;
      const std::unordered_set<TNode>& vars = aletify.getVariables();
      for (TNode v : vars)
      {
        if (v.getKind() == BOUND_VARIABLE)
        {
          outVars << "(declare-var " << v << " " << v.getType() << ")"
                  << std::endl;
        }
      }
      if (options().proof.alfPrintReference)
      {
        // parse_normalize is used as the normalization function for the input
        out << "(reference \"" << options().driver.filename << "\" parse_normalize)"
            << std::endl;
        // [2] print the universal variables
        out << outVars.str();
      }
      else
      {
        // [1] print the types
        smt::PrintBenchmark pb(Printer::getPrinter(out), &d_tproc);
        std::stringstream outFuns;
        pb.printDeclarationsFrom(out, outFuns, definitions, assertions);
        // [2] print the universal variables
        out << outVars.str();
        // [3] print the declared functions
        out << outFuns.str();
      }
      // [4] print proof-level term bindings
      printLetList(out, lbind);
    }
    // [5] print (unique) assumptions
    std::unordered_set<Node> processed;
    for (const Node& n : assertions)
    {
      if (processed.find(n) != processed.end())
      {
        continue;
      }
      processed.insert(n);
      size_t id = allocateAssumeId(n, wasAlloc);
      Node nc = d_tproc.convert(n);
      aout->printAssume(nc, id, false);
    }
    for (const Node& n : definitions)
    {
      if (n.getKind() != EQUAL)
      {
        // skip define-fun-rec?
        continue;
      }
      if (processed.find(n) != processed.end())
      {
        continue;
      }
      processed.insert(n);
      // define-fun are HO equalities that can be proven by refl
      size_t id = allocateAssumeId(n, wasAlloc);
      Node f = d_tproc.convert(n[0]);
      Node lam = d_tproc.convert(n[1]);
      aout->printStep("refl", f.eqNode(lam), id, {}, {lam});
    }
    // [6] print proof body
    printProofInternal(aout, pnBody);
  }
  // if flattened, print the full proof as ident
  if (!d_proofFlatten)
  {
    d_pfIdCounter++;
    std::map<const ProofNode*, Node>::iterator it = d_pnodeMap.find(pnBody);
    if (it != d_pnodeMap.end())
    {
      aprint.printStep(
          "identity", pnBody->getResult(), d_pfIdCounter, {it->second}, {});
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
      Assert(pn->getArguments().size() == 3);
      size_t aid = allocatePush(pn);
      Node a = d_tproc.convert(pn->getArguments()[2]);
      // print a push
      out->printAssume(a, aid, true);
    }
  }
}

void AlfPrinter::getArgsFromPfRule(const ProofNode* pn, std::vector<Node>& args)
{
  Node res = pn->getResult();
  const std::vector<Node> pargs = pn->getArguments();
  PfRule r = pn->getRule();
  switch (r)
  {
    case PfRule::CHAIN_RESOLUTION:
    {
      // we combine into a list
      NodeManager* nm = NodeManager::currentNM();
      Node argsList = nm->mkNode(AND, pargs);
      argsList = d_tproc.convert(argsList);
      args.push_back(argsList);
      return;
    }
    break;
    // several strings proof rules require adding the type as the first argument
    case PfRule::CONCAT_EQ:
    case PfRule::CONCAT_UNIFY:
    case PfRule::CONCAT_CSPLIT:
    {
      Assert(res.getKind() == EQUAL);
      args.push_back(d_tproc.typeAsNode(res[0].getType()));
    }
    break;
    case PfRule::STRING_LENGTH_POS:
      args.push_back(d_tproc.typeAsNode(pargs[0].getType()));
      break;
    case PfRule::STRING_REDUCTION:
    case PfRule::STRING_EAGER_REDUCTION:
    {
      TypeNode towner = theory::strings::utils::getOwnerStringType(pargs[0]);
      args.push_back(d_tproc.typeAsNode(towner));
    }
    break;
    case PfRule::INT_TIGHT_LB:
    case PfRule::INT_TIGHT_UB:
      Assert(res.getNumChildren() == 2);
      // provide the target constant explicitly
      args.push_back(d_tproc.convert(res[1]));
      break;
    case PfRule::ARITH_TRICHOTOMY:
      // argument is redundant
      return;
    case PfRule::INSTANTIATE:
    {
      // ignore arguments past the term vector, collect them into an sexpr
      Node q = pn->getChildren()[0]->getResult();
      Assert(q.getKind() == FORALL);
      // only provide arguments up to the variable list length
      std::vector<Node> targs;
      for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
      {
        Assert(i < pargs.size());
        targs.push_back(d_tproc.convert(pargs[i]));
      }
      // package as list
      Node ts = d_tproc.mkList(targs);
      args.push_back(ts);
      return;
    }
    default: break;
  }
  ProofNodeToSExpr pntse;
  for (size_t i = 0, nargs = pargs.size(); i < nargs; i++)
  {
    ProofNodeToSExpr::ArgFormat f = pntse.getArgumentFormat(pn, i);
    Node av = d_tproc.convert(pntse.getArgument(pargs[i], f));
    args.push_back(av);
  }
}

void AlfPrinter::printStepPost(AlfPrintChannel* out, const ProofNode* pn)
{
  // if we have yet to allocate a proof id, do it now
  bool wasAlloc = false;
  bool isPop = false;
  TNode conclusion = d_tproc.convert(pn->getResult());
  TNode conclusionPrint;
  // print conclusion only if option is set, or this is false
  if (options().proof.proofPrintConclusion || conclusion == d_false)
  {
    conclusionPrint = conclusion;
  }
  PfRule r = pn->getRule();
  std::vector<Node> args;
  bool handled = isHandled(pn);
  if (r == PfRule::ALF_RULE)
  {
    const std::vector<Node> aargs = pn->getArguments();
    Node rn = aargs[0];
    AlfRule ar = getAlfRule(rn);
    // if scope, do pop the assumption from passumeMap
    if (ar == AlfRule::SCOPE)
    {
      isPop = true;
      // note that aargs[1] is not provided, it is consumed as an assumption
    }
    else
    {
      // arguments are converted here
      for (size_t i = 2, nargs = aargs.size(); i < nargs; i++)
      {
        args.push_back(d_tproc.convert(aargs[i]));
      }
    }
  }
  else if (handled)
  {
    getArgsFromPfRule(pn, args);
  }
  const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();
  // if not flattening proofs
  if (!d_proofFlatten)
  {
    std::vector<Node> pargs;
    std::string rname;
    if (!handled)
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
        if (d_pnodeMap.find(pn) == d_pnodeMap.end())
        {
          d_pnodeMap[pn] = allocatePremise(id);
        }
        return;
      }
      pargs.insert(pargs.end(), args.begin(), args.end());
    }
    // otherwise just make the node
    if (d_pnodeMap.find(pn) == d_pnodeMap.end())
    {
      d_pnodeMap[pn] = d_tproc.mkInternalApp(rname, pargs, d_pfType);
    }
    return;
  }
  size_t id = allocateProofId(pn, wasAlloc);
  // if we don't handle the rule, print trust
  if (!handled)
  {
    out->printTrustStep(pn->getRule(), conclusionPrint, id, conclusion);
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

size_t AlfPrinter::allocatePush(const ProofNode* pn)
{
  std::map<const ProofNode*, size_t>::iterator it = d_ppushMap.find(pn);
  if (it != d_ppushMap.end())
  {
    return it->second;
  }
  // pn is a Alf SCOPE
  Node a = pn->getArguments()[2];
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
  d_ppushMap[pn] = aid;
  return aid;
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
  if (itan != d_passumeNodeMap.end())
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
