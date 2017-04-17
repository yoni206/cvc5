/*********************                                                        */
/*! \file theory_model.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of model class
 **/
#include "theory/theory_model.h"

#include "options/smt_options.h"
#include "options/uf_options.h"
#include "options/theory_options.h"
#include "options/quantifiers_options.h"
#include "smt/smt_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/type_enumerator.h"
#include "theory/uf/theory_uf_model.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {

context::Context* TheoryModel::getEeContext() {
  if( d_eeContext==NULL ){
    d_eeContext = new context::Context();
  }
  return d_eeContext;
}

TheoryModel::TheoryModel(theory::eq::EqualityEngineNotify& notify, context::Context* c, std::string name, bool enableFuncModels) :
  d_substitutions(c, false), d_eeContext( NULL ), d_modelBuilt(false), d_keepAlive( getEeContext() ), d_enableFuncModels(enableFuncModels)
{
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );

  d_equalityEngine = new eq::EqualityEngine(notify, d_eeContext, name, true);

  // The kinds we are treating as function application in congruence
  // all operator that have shared term children must go here
  d_equalityEngine->addFunctionKind(kind::APPLY_UF);
  //FIXME : Should these be included?  This is necessary for model-based theory combination since conflicts may be encountered via congruence.
  //        Alternatively, could enforce T-consistency of model by evaluation (option repCheckModels)
  if( options::modelBasedTc() ){
    d_equalityEngine->addFunctionKind(kind::SELECT);
    d_equalityEngine->addFunctionKind(kind::APPLY_CONSTRUCTOR);
    d_equalityEngine->addFunctionKind(kind::APPLY_SELECTOR_TOTAL);
    d_equalityEngine->addFunctionKind(kind::APPLY_TESTER);
    d_equalityEngine->addFunctionKind(kind::STORE);
    d_equalityEngine->addFunctionKind(kind::SINGLETON);
    d_equalityEngine->addFunctionKind(kind::UNION);
    d_equalityEngine->addFunctionKind(kind::INTERSECTION);
    d_equalityEngine->addFunctionKind(kind::SEP_PTO);
    d_equalityEngine->addFunctionKind(kind::MEMBER);
    d_equalityEngine->addFunctionKind(kind::CARD);
    d_equalityEngine->addFunctionKind(kind::STRING_LENGTH);
    d_equalityEngine->addFunctionKind(kind::JOIN);
    d_equalityEngine->addFunctionKind(kind::TCLOSURE);
    d_equalityEngine->addFunctionKind(kind::PRODUCT);
    d_equalityEngine->addFunctionKind(kind::TRANSPOSE);
  }

  d_eeContext->push();
}

TheoryModel::~TheoryModel() throw() {
  d_eeContext->pop();
  delete d_equalityEngine;
  delete d_eeContext;
}

void TheoryModel::reset(){
  d_modelCache.clear();
  d_comment_str.clear();
  d_sep_heap = Node::null();
  d_sep_nil_eq = Node::null();
  d_reps.clear();
  d_rep_set.clear();
  d_uf_terms.clear();
  d_uf_models.clear();
  d_eeContext->pop();
  d_eeContext->push();
}

void TheoryModel::getComments(std::ostream& out) const {
  Trace("model-builder") << "get comments..." << std::endl;
  out << d_comment_str.str();
}

void TheoryModel::setHeapModel( Node h, Node neq ) { 
  d_sep_heap = h;
  d_sep_nil_eq = neq;
}

bool TheoryModel::getHeapModel( Expr& h, Expr& neq ) const {
  if( d_sep_heap.isNull() || d_sep_nil_eq.isNull() ){
    return false;
  }else{
    h = d_sep_heap.toExpr();
    neq = d_sep_nil_eq.toExpr();
    return true;
  }
}

Node TheoryModel::getValue(TNode n, bool useDontCares) const {
  //apply substitutions
  Node nn = d_substitutions.apply(n);
  //get value in model
  nn = getModelValue(nn, false, useDontCares);
  if (nn.isNull()) return nn;
  if(options::condenseFunctionValues() || nn.getKind() != kind::LAMBDA) {
    //normalize
    nn = Rewriter::rewrite(nn);
  }
  Debug("model-getvalue") << "[model-getvalue] getValue( " << n << " ): " << std::endl
                          << "[model-getvalue] returning " << nn << std::endl;
  return nn;
}

bool TheoryModel::isDontCare(Expr expr) const {
  return getValue(Node::fromExpr(expr), true).isNull();
}

Expr TheoryModel::getValue( Expr expr ) const{
  Node n = Node::fromExpr( expr );
  Node ret = getValue( n );
  return d_smt.postprocess(ret, TypeNode::fromType(expr.getType())).toExpr();
}

/** get cardinality for sort */
Cardinality TheoryModel::getCardinality( Type t ) const{
  TypeNode tn = TypeNode::fromType( t );
  //for now, we only handle cardinalities for uninterpreted sorts
  if( tn.isSort() ){
    if( d_rep_set.hasType( tn ) ){
      Debug("model-getvalue-debug") << "Get cardinality sort, #rep : " << d_rep_set.getNumRepresentatives( tn ) << std::endl;
      return Cardinality( d_rep_set.getNumRepresentatives( tn ) );
    }else{
      Debug("model-getvalue-debug") << "Get cardinality sort, unconstrained, return 1." << std::endl;
      return Cardinality( 1 );
    }
  }else{
      Debug("model-getvalue-debug") << "Get cardinality other sort, unknown." << std::endl;
    return Cardinality( CardinalityUnknown() );
  }
}

Node TheoryModel::getModelValue(TNode n, bool hasBoundVars, bool useDontCares) const
{
  std::hash_map<Node, Node, NodeHashFunction>::iterator it = d_modelCache.find(n);
  if (it != d_modelCache.end()) {
    return (*it).second;
  }
  Node ret = n;
  if(n.getKind() == kind::EXISTS || n.getKind() == kind::FORALL || n.getKind() == kind::COMBINED_CARDINALITY_CONSTRAINT ||
     ( n.getKind() == kind::CARDINALITY_CONSTRAINT && options::ufssMode()!=theory::uf::UF_SS_FULL ) ) {
    // We should have terms, thanks to TheoryQuantifiers::collectModelInfo().
    // However, if the Decision Engine stops us early, there might be a
    // quantifier that isn't assigned.  In conjunction with miniscoping, this
    // might lead to a perfectly good model.  Think of
    //     ASSERT FORALL(x) : p OR x=5
    // The p is pulled out by miniscoping, and set to TRUE by the decision
    // engine, then the quantifier's value in the model doesn't matter, so the
    // Decision Engine stops.  So even though the top-level quantifier was
    // asserted, it can't be checked directly: first, it doesn't "exist" in
    // non-miniscoped form, and second, no quantifiers have been asserted, so
    // none is in the model.  We used to fail an assertion here, but that's
    // no good.  Instead, return the quantifier itself.  If we're in
    // checkModel(), and the quantifier actually matters, we'll get an
    // assert-fail since the quantifier isn't a constant.
    Node nr = Rewriter::rewrite(n);
    if(!d_equalityEngine->hasTerm(nr)) {
      d_modelCache[n] = ret;
      return ret;
    } else {
      ret = nr;
    }
  } else {
    if(n.getKind() == kind::LAMBDA) {
      NodeManager* nm = NodeManager::currentNM();
      Node body = getModelValue(n[1], true);
      body = Rewriter::rewrite(body);
      ret = nm->mkNode(kind::LAMBDA, n[0], body);
      d_modelCache[n] = ret;
      return ret;
    }
    if(n.isConst() || (hasBoundVars && n.getKind() == kind::BOUND_VARIABLE)) {
      d_modelCache[n] = ret;
      return ret;
    }

    TypeNode t = n.getType();
    if (t.isFunction() || t.isPredicate()) {
      if (d_enableFuncModels) {
        std::map< Node, Node >::const_iterator it = d_uf_models.find(n);
        if (it != d_uf_models.end()) {
          // Existing function
          ret = it->second;
          d_modelCache[n] = ret;
          return ret;
        }
        // Unknown function symbol: return LAMBDA x. c, where c is the first constant in the enumeration of the range type
        vector<TypeNode> argTypes = t.getArgTypes();
        vector<Node> args;
        NodeManager* nm = NodeManager::currentNM();
        for (unsigned i = 0; i < argTypes.size(); ++i) {
          args.push_back(nm->mkBoundVar(argTypes[i]));
        }
        Node boundVarList = nm->mkNode(kind::BOUND_VAR_LIST, args);
        TypeEnumerator te(t.getRangeType());
        ret = nm->mkNode(kind::LAMBDA, boundVarList, *te);
        d_modelCache[n] = ret;
        return ret;
      }
      // TODO: if func models not enabled, throw an error?
      Unreachable();
    }

    if (n.getNumChildren() > 0 &&
        n.getKind() != kind::BITVECTOR_ACKERMANIZE_UDIV &&
        n.getKind() != kind::BITVECTOR_ACKERMANIZE_UREM) {
      Debug("model-getvalue-debug") << "Get model value children " << n << std::endl;
      std::vector<Node> children;
      if (n.getKind() == APPLY_UF) {
        Node op = getModelValue(n.getOperator(), hasBoundVars);
        Debug("model-getvalue-debug") << "  operator : " << op << std::endl;
        children.push_back(op);
      }
      else if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(n.getOperator());
      }
      //evaluate the children
      for (unsigned i = 0; i < n.getNumChildren(); ++i) {
        ret = getModelValue(n[i], hasBoundVars);
        Debug("model-getvalue-debug") << "  " << n << "[" << i << "] is " << ret << std::endl;
        children.push_back(ret);
      }
      ret = NodeManager::currentNM()->mkNode(n.getKind(), children);
      Debug("model-getvalue-debug") << "ret (pre-rewrite): " << ret << std::endl;
      ret = Rewriter::rewrite(ret);
      Debug("model-getvalue-debug") << "ret (post-rewrite): " << ret << std::endl;
      if(ret.getKind() == kind::CARDINALITY_CONSTRAINT) {
        Debug("model-getvalue-debug") << "get cardinality constraint " << ret[0].getType() << std::endl;
        ret = NodeManager::currentNM()->mkConst(getCardinality(ret[0].getType().toType()).getFiniteCardinality() <= ret[1].getConst<Rational>().getNumerator());
      }else if(ret.getKind() == kind::CARDINALITY_VALUE) {
        Debug("model-getvalue-debug") << "get cardinality value " << ret[0].getType() << std::endl;
        ret = NodeManager::currentNM()->mkConst(Rational(getCardinality(ret[0].getType().toType()).getFiniteCardinality()));
      }
      d_modelCache[n] = ret;
      return ret;
    }

    if (!d_equalityEngine->hasTerm(n)) {
      if(n.getType().isRegExp()) {
        ret = Rewriter::rewrite(ret);
      } else {
        if (options::omitDontCares() && useDontCares) {
          return Node();
        }
        // Unknown term - return first enumerated value for this type
        TypeEnumerator te(n.getType());
        ret = *te;
      }
      d_modelCache[n] = ret;
      return ret;
    }
  }
  ret = d_equalityEngine->getRepresentative(ret);
  Debug("model-getvalue-debug") << "Representative value is " << ret << std::endl;
  Assert(d_reps.find(ret) != d_reps.end());
  std::map< Node, Node >::const_iterator it2 = d_reps.find( ret );
  if (it2 != d_reps.end()) {
    ret = it2->second;
    Debug("model-getvalue-debug") << "Return value is " << ret << std::endl;
  }
  Assert( ret.isConst() );
  d_modelCache[n] = ret;
  return ret;
}

Node TheoryModel::getDomainValue( TypeNode tn, std::vector< Node >& exclude ){
  if( d_rep_set.d_type_reps.find( tn )!=d_rep_set.d_type_reps.end() ){
    //try to find a pre-existing arbitrary element
    for( size_t i=0; i<d_rep_set.d_type_reps[tn].size(); i++ ){
      if( std::find( exclude.begin(), exclude.end(), d_rep_set.d_type_reps[tn][i] )==exclude.end() ){
        return d_rep_set.d_type_reps[tn][i];
      }
    }
  }
  return Node::null();
}

/** add substitution */
void TheoryModel::addSubstitution( TNode x, TNode t, bool invalidateCache ){
  if( !d_substitutions.hasSubstitution( x ) ){
    d_substitutions.addSubstitution( x, t, invalidateCache );
  } else {
#ifdef CVC4_ASSERTIONS
    Node oldX = d_substitutions.getSubstitution(x);
    // check that either the old substitution is the same, or it now maps to the new substitution
    if(oldX != t && d_substitutions.apply(oldX) != d_substitutions.apply(t)) {
      stringstream ss;
      ss << "Two incompatible substitutions added to TheoryModel:\n"
         << "the term:    " << x << "\n"
         << "old mapping: " << d_substitutions.apply(oldX) << "\n"
         << "new mapping: " << d_substitutions.apply(t);
      InternalError(ss.str());
    }
#endif /* CVC4_ASSERTIONS */
  }
}

/** add term */
void TheoryModel::addTerm(TNode n ){
  Assert(d_equalityEngine->hasTerm(n));
  //must collect UF terms
  if (n.getKind()==APPLY_UF) {
    Node op = n.getOperator();
    if( std::find( d_uf_terms[ op ].begin(), d_uf_terms[ op ].end(), n )==d_uf_terms[ op ].end() ){
      d_uf_terms[ op ].push_back( n );
      Trace("model-add-term-uf") << "Add term " << n << std::endl;
    }
  }
}

/** assert equality */
bool TheoryModel::assertEquality(TNode a, TNode b, bool polarity ){
  Assert(d_equalityEngine->consistent());
  if (a == b && polarity) {
    return true;
  }
  Node reason;
  if( polarity ){
    reason = a.eqNode(b);
  }else{
    reason = a.eqNode(b).negate();
  }
  return assertEquality( a, b, polarity, reason );
}

bool TheoryModel::assertEquality(TNode a, TNode b, bool polarity, Node reason) {
  Assert(d_equalityEngine->consistent());
  if (a == b && polarity) {
    return true;
  }
  Node eq = a.eqNode(b);
  Trace("model-builder-assertions") << "(assert " << (polarity ? "(= " : "(not (= ") << a << " " << b << (polarity ? "));" : ")));") << endl;
  d_keepAlive.push_back( reason );
  d_equalityEngine->assertEquality( eq, polarity, reason );
  return d_equalityEngine->consistent();
}

/** assert predicate */
bool TheoryModel::assertPredicate(TNode a, bool polarity ){
  Assert(d_equalityEngine->consistent());
  if ((a == d_true && polarity) ||
      (a == d_false && (!polarity))) {
    return true;
  }
  Node exp;
  if( polarity ){
    exp = a;
  }else{
    exp = a.negate();
  }
  d_keepAlive.push_back( exp );
  if (a.getKind() == EQUAL) {
    Trace("model-builder-assertions") << "(assert " << (polarity ? " " : "(not ") << a << (polarity ? ");" : "));") << endl;
    d_equalityEngine->assertEquality( a, polarity, exp );
  } else {
    Trace("model-builder-assertions") << "(assert " << (polarity ? "" : "(not ") << a << (polarity ? ");" : "));") << endl;
    d_equalityEngine->assertPredicate( a, polarity, exp );
  }
  return d_equalityEngine->consistent();
}

/** assert equality engine */
bool TheoryModel::assertEqualityEngine(const eq::EqualityEngine* ee, theory::TheoryId tid, set<Node>* termSet){
  Assert(d_equalityEngine->consistent());
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  for (; !eqcs_i.isFinished(); ++eqcs_i) {
    Node eqc = (*eqcs_i);
    bool predicate = false;
    bool predTrue = false;
    bool predFalse = false;
    if (eqc.getType().isBoolean()) {
      predicate = true;
      predTrue = ee->areEqual(eqc, d_true);
      predFalse = ee->areEqual(eqc, d_false);
    }
    
    //make the representative a shared term (for model-based theory combination)
    Node rep;
    if( ee->isTriggerTerm( eqc, tid ) ){
      rep = ee->getTriggerTermRepresentative(eqc, tid);
    }
    
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
    for (; !eqc_i.isFinished(); ++eqc_i) {
      if (termSet != NULL && termSet->find(*eqc_i) == termSet->end()) {
        Trace("model-builder-debug") << "...skip " << (*eqc_i) << std::endl;
        continue;
      }
      if( rep.isNull() ){
        rep = (*eqc_i);
      }
      if (predicate) {
        if (predTrue) {
          if( !assertPredicate(*eqc_i, true) ){
            return false;
          }
        }
        else if (predFalse) {
          if( !assertPredicate(*eqc_i, false) ){
            return false;
          }
        }
        else {
          if ((*eqc_i)!=rep) {
            Trace("model-builder-assertions") << "(assert (= " << *eqc_i << " " << rep << "));" << endl;
            d_equalityEngine->mergePredicates(*eqc_i, rep, Node::null());
            if(!d_equalityEngine->consistent()){
              return false;
            }
          }
        }
      } else {
        if ((*eqc_i)==rep) {
          //add the term (this is specifically for the case of singleton equivalence classes)
          if( !rep.getType().isRegExp() ){
            d_equalityEngine->addTerm( rep );
            Trace("model-builder-debug") << "Add term to ee within assertEqualityEngine: " << rep << std::endl;
          }
        }
        else {
          if( !assertEquality(*eqc_i, rep, true) ){
            return false;
          }
        }
      }
    }
  }
  Assert(d_equalityEngine->consistent());
  return true;
}

void TheoryModel::assertRepresentative(TNode n )
{
  Trace("model-builder-reps") << "Assert rep : " << n << std::endl;
  Trace("model-builder-reps") << "Rep eqc is : " << getRepresentative( n ) << std::endl;
  d_reps[ n ] = n;
}

bool TheoryModel::hasTerm(TNode a)
{
  return d_equalityEngine->hasTerm( a );
}

Node TheoryModel::getRepresentative(TNode a)
{
  if( d_equalityEngine->hasTerm( a ) ){
    Node r = d_equalityEngine->getRepresentative( a );
    //TODO: remove this (representatives should be true in the ee with new implementation)
    if( d_reps.find( r )!=d_reps.end() ){
      return d_reps[ r ];
    }else{
      return r;
    }
  }else{
    return a;
  }
}

bool TheoryModel::areEqual(TNode a, TNode b)
{
  if( a==b ){
    return true;
  }else if( d_equalityEngine->hasTerm( a ) && d_equalityEngine->hasTerm( b ) ){
    return d_equalityEngine->areEqual( a, b );
  }else{
    return false;
  }
}

bool TheoryModel::areDisequal(TNode a, TNode b)
{
  if( d_equalityEngine->hasTerm( a ) && d_equalityEngine->hasTerm( b ) ){
    return d_equalityEngine->areDisequal( a, b, false );
  }else{
    return false;
  }
}

//for debugging
void TheoryModel::printRepresentativeDebug( const char* c, Node r ){
  if( r.isNull() ){
    Trace( c ) << "null";
  }else if( r.getType().isBoolean() ){
    if( areEqual( r, d_true ) ){
      Trace( c ) << "true";
    }else{
      Trace( c ) << "false";
    }
  }else{
    Trace( c ) << getRepresentative( r );
  }
}

void TheoryModel::printRepresentative( std::ostream& out, Node r ){
  Assert( !r.isNull() );
  if( r.isNull() ){
    out << "null";
  }else if( r.getType().isBoolean() ){
    if( areEqual( r, d_true ) ){
      out  << "true";
    }else{
      out  << "false";
    }
  }else{
    out << getRepresentative( r );
  }
}


TheoryEngineModelBuilder::TheoryEngineModelBuilder( TheoryEngine* te ) : d_te( te ){

}


bool TheoryEngineModelBuilder::isAssignable(TNode n)
{
  return (n.isVar() || n.getKind() == kind::APPLY_UF || n.getKind() == kind::SELECT || n.getKind() == kind::APPLY_SELECTOR_TOTAL);
}


void TheoryEngineModelBuilder::checkTerms(TNode n, TheoryModel* tm, NodeSet& cache)
{
  if (n.getKind()==FORALL || n.getKind()==EXISTS) {
    return;
  }
  if (cache.find(n) != cache.end()) {
    return;
  }
  if (isAssignable(n)) {
    tm->d_equalityEngine->addTerm(n);
  }
  for(TNode::iterator child_it = n.begin(); child_it != n.end(); ++child_it) {
    checkTerms(*child_it, tm, cache);
  }
  cache.insert(n);
}

void TheoryEngineModelBuilder::assignConstantRep( TheoryModel* tm, Node const_rep, Node term_rep ) {
  Assert( tm->getRepresentative( const_rep )==const_rep );
  //Assert( tm->getRepresentative( term_rep )==const_rep );
  //FIXME : remove constantReps
  d_constantReps[const_rep] = const_rep;
  //Trace("model-builder-debug") << "......assign: Setting constant rep of " << eqc << " to " << const_rep << ", term rep is " << term_rep << endl;
  tm->d_rep_set.d_values_to_terms[const_rep] = term_rep;
}

bool TheoryEngineModelBuilder::isExcludedCdtValue( Node val, std::set<Node>* repSet, std::map< Node, Node >& assertedReps, Node eqc ) {
  Trace("model-builder-debug") << "Is " << val << " and excluded codatatype value for " << eqc << "? " << std::endl;
  for (set<Node>::iterator i = repSet->begin(); i != repSet->end(); ++i ) {
    Assert(assertedReps.find(*i) != assertedReps.end());
    Node rep = assertedReps[*i];
    Trace("model-builder-debug") << "  Rep : " << rep << std::endl;
    //check matching val to rep with eqc as a free variable
    Node eqc_m;
    if( isCdtValueMatch( val, rep, eqc, eqc_m ) ){
      Trace("model-builder-debug") << "  ...matches with " << eqc << " -> " << eqc_m << std::endl;
      if( eqc_m.getKind()==kind::UNINTERPRETED_CONSTANT ){
        Trace("model-builder-debug") << "*** " << val << " is excluded datatype for " << eqc << std::endl;
        return true;
      }
    }
  }
  return false;
}

bool TheoryEngineModelBuilder::isCdtValueMatch( Node v, Node r, Node eqc, Node& eqc_m ) {
  if( r==v ){
    return true;
  }else if( r==eqc ){
    if( eqc_m.isNull() ){
      //only if an uninterpreted constant?
      eqc_m = v;
      return true;
    }else{
      return v==eqc_m;
    }
  }else if( v.getKind()==kind::APPLY_CONSTRUCTOR && r.getKind()==kind::APPLY_CONSTRUCTOR ){
    if( v.getOperator()==r.getOperator() ){
      for( unsigned i=0; i<v.getNumChildren(); i++ ){
        if( !isCdtValueMatch( v[i], r[i], eqc, eqc_m ) ){
          return false;
        }
      }
      return true;
    }
  }
  return false;
}

bool TheoryEngineModelBuilder::involvesUSort( TypeNode tn ) {
  if( tn.isSort() ){
    return true;
  }else if( tn.isArray() ){
    return involvesUSort( tn.getArrayIndexType() ) || involvesUSort( tn.getArrayConstituentType() );
  }else if( tn.isSet() ){
    return involvesUSort( tn.getSetElementType() );
  }else if( tn.isDatatype() ){
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    return dt.involvesUninterpretedType();
  }else{
    return false;
  }
}

bool TheoryEngineModelBuilder::isExcludedUSortValue( std::map< TypeNode, unsigned >& eqc_usort_count, Node v, std::map< Node, bool >& visited ) {
  Assert( v.isConst() );
  if( visited.find( v )==visited.end() ){
    visited[v] = true;
    TypeNode tn = v.getType();
    if( tn.isSort() ){
      Trace("model-builder-debug") << "Is excluded usort value : " << v << " " << tn << std::endl;
      unsigned card = eqc_usort_count[tn];
      Trace("model-builder-debug") << "  Cardinality is " << card << std::endl;
      unsigned index = v.getConst<UninterpretedConstant>().getIndex().toUnsignedInt();
      Trace("model-builder-debug") << "  Index is " << index << std::endl;
      return index>0 && index>=card;
    }
    for( unsigned i=0; i<v.getNumChildren(); i++ ){
      if( isExcludedUSortValue( eqc_usort_count, v[i], visited ) ){
        return true;
      }
    }
  }
  return false;
}

bool TheoryEngineModelBuilder::buildModel(Model* m)
{
  Trace("model-builder") << "TheoryEngineModelBuilder: buildModel" << std::endl;
  TheoryModel* tm = (TheoryModel*)m;

  // buildModel should only be called once per check
  Assert(!tm->isBuilt());
  tm->d_modelBuilt = true;

  // Reset model
  tm->reset();

  // Collect model info from the theories
  Trace("model-builder") << "TheoryEngineModelBuilder: Collect model info..." << std::endl;
  if( !d_te->collectModelInfo(tm) ){
    return false;
  }  

  // model-builder specific initialization
  if( !preProcessBuildModel(tm) ){
    return false;
  }

  // Loop through all terms and make sure that assignable sub-terms are in the equality engine
  // Also, record #eqc per type (for finite model finding)
  std::map< TypeNode, unsigned > eqc_usort_count;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( tm->d_equalityEngine );
  {
    NodeSet cache;
    for ( ; !eqcs_i.isFinished(); ++eqcs_i) {
      eq::EqClassIterator eqc_i = eq::EqClassIterator((*eqcs_i),tm->d_equalityEngine);
      for ( ; !eqc_i.isFinished(); ++eqc_i) {
        checkTerms(*eqc_i, tm, cache);
      }
      TypeNode tn = (*eqcs_i).getType();
      if( tn.isSort() ){
        if( eqc_usort_count.find( tn )==eqc_usort_count.end() ){
          eqc_usort_count[tn] = 1;
        }else{
          eqc_usort_count[tn]++;
        }
      }
    }
  }

  Trace("model-builder") << "Collect representatives..." << std::endl;

  // Process all terms in the equality engine, store representatives for each EC
  d_constantReps.clear();
  std::map< Node, Node > assertedReps;
  TypeSet typeConstSet, typeRepSet, typeNoRepSet;
  TypeEnumeratorProperties tep;
  if( options::finiteModelFind() ){
    tep.d_fixed_usort_card = true;
    for( std::map< TypeNode, unsigned >::iterator it = eqc_usort_count.begin(); it != eqc_usort_count.end(); ++it ){
      Trace("model-builder") << "Fixed bound (#eqc) for " << it->first << " : " << it->second << std::endl;
      tep.d_fixed_card[it->first] = Integer(it->second);
    }
    typeConstSet.setTypeEnumeratorProperties( &tep );
  }
  std::set< TypeNode > allTypes;
  eqcs_i = eq::EqClassesIterator(tm->d_equalityEngine);
  for ( ; !eqcs_i.isFinished(); ++eqcs_i) {

    // eqc is the equivalence class representative
    Node eqc = (*eqcs_i);
    Trace("model-builder") << "Processing EC: " << eqc << endl;
    Assert(tm->d_equalityEngine->getRepresentative(eqc) == eqc);
    TypeNode eqct = eqc.getType();
    Assert(assertedReps.find(eqc) == assertedReps.end());
    Assert(d_constantReps.find(eqc) == d_constantReps.end());

    // Loop through terms in this EC
    Node rep, const_rep;
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, tm->d_equalityEngine);
    for ( ; !eqc_i.isFinished(); ++eqc_i) {
      Node n = *eqc_i;
      Trace("model-builder") << "  Processing Term: " << n << endl;
      // Record as rep if this node was specified as a representative
      if (tm->d_reps.find(n) != tm->d_reps.end()){
        //AJR: I believe this assertion is too strict, 
        // e.g. datatypes may assert representative for two constructor terms that are not in the care graph and are merged during collectModelInfo.
        //Assert(rep.isNull());
        rep = tm->d_reps[n];
        Assert(!rep.isNull() );
        Trace("model-builder") << "  Rep( " << eqc << " ) = " << rep << std::endl;
      }
      // Record as const_rep if this node is constant
      if (n.isConst()) {
        Assert(const_rep.isNull());
        const_rep = n;
        Trace("model-builder") << "  ConstRep( " << eqc << " ) = " << const_rep << std::endl;
      }
      //model-specific processing of the term
      tm->addTerm(n);
    }

    // Assign representative for this EC
    if (!const_rep.isNull()) {
      // Theories should not specify a rep if there is already a constant in the EC
      //AJR: I believe this assertion is too strict, eqc with asserted reps may merge with constant eqc
      //Assert(rep.isNull() || rep == const_rep);
      Assert( eqc==const_rep );
      assignConstantRep( tm, const_rep, eqc );
      typeConstSet.add(eqct.getBaseType(), const_rep);
    }else if (!rep.isNull()) {
      assertedReps[eqc] = rep;
      typeRepSet.add(eqct.getBaseType(), eqc);
      allTypes.insert(eqct.getBaseType());
    }else{
      typeNoRepSet.add(eqct, eqc);
      allTypes.insert(eqct);
    }
  }

  // Need to ensure that each EC has a constant representative.

  Trace("model-builder") << "Processing EC's..." << std::endl;

  TypeSet::iterator it;
  set<TypeNode>::iterator type_it;
  set<Node>::iterator i, i2;
  bool changed, unassignedAssignable, assignOne = false;
  set<TypeNode> evaluableSet;

  // Double-fixed-point loop
  // Outer loop handles a special corner case (see code at end of loop for details)
  for (;;) {

    // Inner fixed-point loop: we are trying to learn constant values for every EC.  Each time through this loop, we process all of the
    // types by type and may learn some new EC values.  EC's in one type may depend on EC's in another type, so we need a fixed-point loop
    // to ensure that we learn as many EC values as possible
    do {
      changed = false;
      unassignedAssignable = false;
      evaluableSet.clear();

      // Iterate over all types we've seen
      for (type_it = allTypes.begin(); type_it != allTypes.end(); ++type_it) {
        TypeNode t = *type_it;
        TypeNode tb = t.getBaseType();
        set<Node>* noRepSet = typeNoRepSet.getSet(t);

        // 1. Try to evaluate the EC's in this type
        if (noRepSet != NULL && !noRepSet->empty()) {
          Trace("model-builder") << "  Eval phase, working on type: " << t << endl;
          bool assignable, evaluable, evaluated;
          d_normalizedCache.clear();
          d_normalizedCacheExp.clear();
          for (i = noRepSet->begin(); i != noRepSet->end(); ) {
            i2 = i;
            ++i;
            assignable = false;
            evaluable = false;
            evaluated = false;
            Node r = *i2;
            if( tm->getRepresentative( r )!=r ){
              // this representative was merge with something else
              noRepSet->erase(i2);
              Trace("model-builder-debug") << "....eqc " << r << " was merged." << std::endl; 
            }else{            
              Trace("model-builder-debug") << "....look at eqc " << r << std::endl; 
              eq::EqClassIterator eqc_i = eq::EqClassIterator(r, tm->d_equalityEngine);
              for ( ; !eqc_i.isFinished(); ++eqc_i) {
                Node n = *eqc_i;
                if (isAssignable(n)) {
                  assignable = true;
                }
                else {
                  evaluable = true;
                  std::vector< Node > expl;
                  Node normalized = normalize(tm, n, true, expl);
                  if (normalized.isConst()) {
                    Trace("model-builder-debug") << "....normalized " << n << " to " << normalized << ", with explanation size = " << expl.size() << std::endl;
                    Node exp;
                    if( expl.size()==1 ){
                      Trace("model-builder-debug") << "......explanation is " << expl[0] << std::endl;
                      exp = expl[0];
                    }else{
                      //Assert( false );
                      exp = n.eqNode( normalized );
                      // can occur for sets { 0, 1 } -> { 1, 0 } for some reason
                    }
                    Trace("model-builder") << "    *** Eval: Setting constant rep of " << n << " to " << normalized << std::endl;
                    //must assert the equality
                    if( !tm->assertEquality( n, normalized, true, exp ) ){
                      return false;
                    }
                    //get the representative again (may have updated)
                    typeConstSet.add(tb, normalized);
                    Assert( tm->getRepresentative( n )==normalized );
                    assignConstantRep( tm, normalized, r);
                    changed = true;
                    evaluated = true;
                    noRepSet->erase(i2);
                    break;
                  }
                }
              }
            }
            if (!evaluated) {
              if (evaluable) {
                evaluableSet.insert(tb);
              }
              if (assignable) {
                unassignedAssignable = true;
              }
            }
          }
        }

        // 2. Normalize any non-const representative terms for this type
        set<Node>* repSet = typeRepSet.getSet(t);
        if (repSet != NULL && !repSet->empty()) {
          Trace("model-builder") << "  Normalization phase, working on type: " << t << endl;
          d_normalizedCache.clear();
          d_normalizedCacheExp.clear();
          for (i = repSet->begin(); i != repSet->end(); ) {
            Assert(assertedReps.find(*i) != assertedReps.end());
            Node r = *i;
            // notice that r may no longer be its own representative.
            // However, we need to evaluate its asserted representative to satisfy contract with theory.
            Node rep = assertedReps[r];
            std::vector< Node > expl;
            Trace("model-builder-debug") << "....normalizing rep of " << r << ", which has asserted rep " << rep << std::endl;
            Node normalized = normalize(tm, rep, false, expl);
            if (normalized.isConst()) {
              Trace("model-builder-debug") << "....normalized " << rep << " to " << normalized << ", with explanation size = " << expl.size() << std::endl;
              Node exp;
              if( expl.size()==1 ){
                Trace("model-builder-debug") << "......explanation is " << expl[0] << std::endl;
                exp = expl[0];
              }else{
                //Assert( false );
                exp = r.eqNode( normalized );
              }
              Trace("model-builder") << "    *** Eval non-constant rep: Setting constant rep of " << r << " to " << normalized << endl;
              //must assert the equality
              //if( !tm->assertEquality( r, normalized, true, expl[0] ) ){
              if( !tm->assertEquality( r, normalized, true, exp ) ){
                return false;
              }
              changed = true;
              typeConstSet.add(tb, normalized);
              Assert( tm->getRepresentative( r )==normalized );
              assignConstantRep( tm, normalized, rep);
              assertedReps.erase(*i);
              i2 = i;
              ++i;
              repSet->erase(i2);
            }else{
              //FIXME : this seems to just be an optimization
              //        may break invariant that model conflicts are explainable by shared term equalities
              //if (normalized != rep) {
              //  assertedReps[*i] = normalized;
              //  changed = true;
              //}
              ++i;
            }
          }
        }
      }
    } while (changed);

    if (!unassignedAssignable) {
      break;
    }

    // 3. Assign unassigned assignable EC's using type enumeration - assign a value *different* from all other EC's if the type is infinite
    // Assign first value from type enumerator otherwise - for finite types, we rely on polite framework to ensure that EC's that have to be
    // different are different.

    // Only make assignments on a type if:
    // 1. there are no terms that share the same base type with un-normalized representatives
    // 2. there are no terms that share teh same base type that are unevaluated evaluable terms
    // Alternatively, if 2 or 3 don't hold but we are in a special deadlock-breaking mode where assignOne is true, go ahead and make one assignment
    changed = false;
    for (it = typeNoRepSet.begin(); it != typeNoRepSet.end(); ++it) {
      set<Node>& noRepSet = TypeSet::getSet(it);
      if (noRepSet.empty()) {
        continue;
      }
      TypeNode t = TypeSet::getType(it);
      
      //get properties of this type
      bool isCorecursive = false;
      if( t.isDatatype() ){
        const Datatype& dt = ((DatatypeType)(t).toType()).getDatatype();
        isCorecursive = dt.isCodatatype() && ( !dt.isFinite( t.toType() ) || dt.isRecursiveSingleton( t.toType() ) );
      }
#ifdef CVC4_ASSERTIONS
      bool isUSortFiniteRestricted = false;
      if( options::finiteModelFind() ){
        isUSortFiniteRestricted = !t.isSort() && involvesUSort( t );
      }
#endif
      
      set<Node>* repSet = typeRepSet.getSet(t);
      TypeNode tb = t.getBaseType();
      if (!assignOne) {
        set<Node>* repSet = typeRepSet.getSet(tb);
        if (repSet != NULL && !repSet->empty()) {
          continue;
        }
        if (evaluableSet.find(tb) != evaluableSet.end()) {
          continue;
        }
      }
      Trace("model-builder") << "  Assign phase, working on type: " << t << endl;
      bool assignable, evaluable CVC4_UNUSED;
      for (i = noRepSet.begin(); i != noRepSet.end(); ) {
        i2 = i;
        ++i;
        Node r = *i2;
        if( tm->getRepresentative( r )!=r ){
          // this representative was merge with something else
          noRepSet.erase(i2);
          Trace("model-builder-debug") << "....eqc " << r << " was merged." << std::endl;
        }else{
          eq::EqClassIterator eqc_i = eq::EqClassIterator(*i2, tm->d_equalityEngine);
          assignable = false;
          evaluable = false;
          for ( ; !eqc_i.isFinished(); ++eqc_i) {
            Node n = *eqc_i;
            if (isAssignable(n)) {
              assignable = true;
            }
            else {
              evaluable = true;
            }
          }
          Trace("model-builder-debug") << "....try eqc " << r << " is assignable=" << assignable << ", evaluable=" << evaluable << std::endl;
          if (assignable) {
            Assert(!evaluable || assignOne);
            Assert(!t.isBoolean() || (*i2).getKind() == kind::APPLY_UF);
            Node n;
            if (t.getCardinality().isInfinite()) {
            // if (!t.isInterpretedFinite()) {
              bool success;
              do{
                Trace("model-builder-debug") << "    enumerate term of type " << t << std::endl;
                n = typeConstSet.nextTypeEnum(t, true);
                //--- AJR: this code checks whether n is a legal value
                Assert( !n.isNull() );
                success = true;
                Trace("model-builder-debug") << "    check if excluded : " << n << std::endl;
  #ifdef CVC4_ASSERTIONS
                if( isUSortFiniteRestricted ){
                  //must not involve uninterpreted constants beyond cardinality bound (which assumed to coincide with #eqc)
                  //this is just an assertion now, since TypeEnumeratorProperties should ensure that only legal values are enumerated wrt this constraint.
                  std::map< Node, bool > visited;
                  success = !isExcludedUSortValue( eqc_usort_count, n, visited );
                  if( !success ){
                    Trace("model-builder-debug") << "    excluded value for " << t << " : " << n << " due to out of range uninterpreted constant." << std::endl;
                  }
                  Assert( success );
                }
  #endif
                if( success && isCorecursive ){
                  if (repSet != NULL && !repSet->empty()) {
                    // in the case of codatatypes, check if it is in the set of values that we cannot assign
                    // this will check whether n \not\in V^x_I from page 9 of Reynolds/Blanchette CADE 2015
                    success = !isExcludedCdtValue( n, repSet, assertedReps, *i2 );
                    if( !success ){
                      Trace("model-builder-debug") << "    excluded value : " << n << " due to alpha-equivalent codatatype expression." << std::endl;
                    }
                  }
                }
                //---
              }while( !success );
            }
            else {
              TypeEnumerator te(t);
              n = *te;
            }
            Assert(!n.isNull());
            Trace("model-builder-debug") << "    assign : " << n << std::endl;
            
            //must assert the equality
            if( !tm->assertEquality( r, n, true ) ){
              //it is strange that we would fail here  TODO : revisit if this should be possible
              //Assert( false );
              return false;
            }
            //get the representative again (may have updated)
            Assert( tm->getRepresentative( *i2 )==n );
            assignConstantRep( tm, n, *i2 );
            changed = true;
            noRepSet.erase(i2);
            if (assignOne) {
              assignOne = false;
              break;
            }
          }
        }
      }
    }

    // Corner case - I'm not sure this can even happen - but it's theoretically possible to have a cyclical dependency
    // in EC assignment/evaluation, e.g. EC1 = {a, b + 1}; EC2 = {b, a - 1}.  In this case, neither one will get assigned because we are waiting
    // to be able to evaluate.  But we will never be able to evaluate because the variables that need to be assigned are in
    // these same EC's.  In this case, repeat the whole fixed-point computation with the difference that the first EC
    // that has both assignable and evaluable expressions will get assigned.
    if (!changed) {
      Assert(!assignOne); // check for infinite loop!
      assignOne = true;
    }
  }
  
#ifdef CVC4_ASSERTIONS
  // Assert that all representatives have been converted to constants
  for (it = typeRepSet.begin(); it != typeRepSet.end(); ++it) {
    set<Node>& repSet = TypeSet::getSet(it);
    if (!repSet.empty()) {
      Node r = *(repSet.begin());
      Node rr = tm->getRepresentative( r );
      Trace("model-builder") << "***Non-empty repSet, size = " << repSet.size() << ", first = " << r << ", rep = " << rr << ", hasTerm = " << tm->hasTerm( r ) << endl;
      Assert(false);
    }
  }
#endif /* CVC4_ASSERTIONS */

  Trace("model-builder") << "Copy representatives to model..." << std::endl;
  tm->d_reps.clear();
  std::map< Node, Node >::iterator itMap;
  for (itMap = d_constantReps.begin(); itMap != d_constantReps.end(); ++itMap) {
    Trace("model-builder")  << "...constant rep : " << itMap->first << " -> " << itMap->second << std::endl;
    tm->d_reps[itMap->first] = itMap->second;
    tm->d_rep_set.add(itMap->second.getType(), itMap->second);
  }

  Trace("model-builder") << "Make sure ECs have reps..." << std::endl;
  // Make sure every EC has a rep
  for (itMap = assertedReps.begin(); itMap != assertedReps.end(); ++itMap ) {
    Trace("model-builder")  << "...asserted rep : " << itMap->first << " -> " << itMap->second << std::endl;
    tm->d_reps[itMap->first] = itMap->second;
    tm->d_rep_set.add(itMap->second.getType(), itMap->second);
  }
  for (it = typeNoRepSet.begin(); it != typeNoRepSet.end(); ++it) {
    set<Node>& noRepSet = TypeSet::getSet(it);
    set<Node>::iterator i;
    for (i = noRepSet.begin(); i != noRepSet.end(); ++i) {
      tm->d_reps[*i] = *i;
      tm->d_rep_set.add((*i).getType(), *i);
    }
  }
  
  // now, do rep checking
  if( options::repCheckModels() ){
    d_normalizedCache.clear();
    d_normalizedCacheExp.clear();
    eqcs_i = eq::EqClassesIterator( tm->d_equalityEngine );
    // Check that every term evaluates to its representative in the model
    for (eqcs_i = eq::EqClassesIterator(tm->d_equalityEngine); !eqcs_i.isFinished(); ++eqcs_i) {
      // eqc is the equivalence class representative
      Node eqc = (*eqcs_i);
      Trace("rep-checking-debug") << "Rep checking for equivalence class " << eqc << "..." << std::endl;
      Node rep;
      if( eqc.isConst() ){
        rep = eqc;
      }else{
        Assert( false );
      }
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, tm->d_equalityEngine);
      for ( ; !eqc_i.isFinished(); ++eqc_i) {
        Node n = *eqc_i;
        // non-linear mult is not necessarily accurate wrt getValue
        if( n!=rep && n.getKind()!=kind::APPLY_UF && n.getKind()!=kind::NONLINEAR_MULT && n.getKind()!=kind::FORALL ){
          if( n.getNumChildren()>0 ){
            std::vector< Node > expl;
            Node normalized = normalize(tm, n, true, expl);
            Trace("rep-checking-debug") << "...check : " << n << " normalized to " << normalized << ", with explanation size = " << expl.size() << std::endl;
            Assert( normalized.isConst() );
            if( normalized!=rep ){
              Trace("rep-checking") << "Rep check fail : " << n << " normalized to " << normalized << std::endl;
              Trace("rep-checking") << "...but rep is  : " << rep << std::endl;
              Node exp;
              if( expl.size()==1 ){
                Trace("rep-checking") << "......explanation is " << expl[0] << std::endl;
                exp = expl[0];
              }else{
                //Assert( false );
                exp = n.eqNode( normalized );
              }
              if( !tm->assertEquality( n, normalized, true, exp ) ){
                return false;
              }else{
                // normalizing to a different constant should definitely lead to a conflict
                Assert( false );
              }
            }
          }
        }
      }
    }
  }

  //modelBuilder-specific initialization
  if( !processBuildModel( tm ) ){
    return false;
  }else{
    return true;
  }
}

void TheoryEngineModelBuilder::debugCheckModel(Model* m){
  TheoryModel* tm = (TheoryModel*)m;
#ifdef CVC4_ASSERTIONS
  Assert(tm->isBuilt());
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( tm->d_equalityEngine );
  std::map< Node, Node >::iterator itMap;
  // Check that every term evaluates to its representative in the model
  for (eqcs_i = eq::EqClassesIterator(tm->d_equalityEngine); !eqcs_i.isFinished(); ++eqcs_i) {
    // eqc is the equivalence class representative
    Node eqc = (*eqcs_i);
    Debug("check-model::rep-checking") << "Rep checking for equivalence class " << eqc << "..." << std::endl;
    Node rep;
    if( eqc.isConst() ){
      rep = eqc;
    }else{
      Assert( false );
      itMap = d_constantReps.find(eqc);
      if (itMap == d_constantReps.end() && eqc.getType().isBoolean()) {
        rep = tm->getValue(eqc);
        Assert(rep.isConst());
      }
      else {
        Assert(itMap != d_constantReps.end());
        rep = itMap->second;
      }
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, tm->d_equalityEngine);
    for ( ; !eqc_i.isFinished(); ++eqc_i) {
      Node n = *eqc_i;
      static int repCheckInstance = 0;
      ++repCheckInstance;
      
      // non-linear mult is not necessarily accurate wrt getValue
      if( n.getKind()!=kind::NONLINEAR_MULT ){
        Debug("check-model::rep-checking")
          << "( " << repCheckInstance <<") "
          << "n: " << n << endl
          << "getValue(n): " << tm->getValue(n) << endl
          << "rep: " << rep << endl;
        Assert(tm->getValue(*eqc_i) == rep, "run with -d check-model::rep-checking for details");
      }
    }
  }
#endif /* CVC4_ASSERTIONS */
  debugModel( tm );
}

Node TheoryEngineModelBuilder::normalize(TheoryModel* m, TNode r, bool evalOnly, std::vector< Node >& expl)
{
  std::map<Node, Node>::iterator itMap = d_constantReps.find(r);
  if (itMap != d_constantReps.end()) {
    Assert( r==(*itMap).second );
    return (*itMap).second;
  }
  NodeMap::iterator it = d_normalizedCache.find(r);
  if (it != d_normalizedCache.end()) {
    NodeMap::iterator itex = d_normalizedCacheExp.find(r);
    if( itex!=d_normalizedCacheExp.end() ){
      expl.push_back( (*itex).second );
    }
    return (*it).second;
  }
  Node retNode = r;
  if (r.getNumChildren() > 0) {
    std::vector<Node> children;
    if (r.getMetaKind() == kind::metakind::PARAMETERIZED) {
      children.push_back(r.getOperator());
    }
    bool childrenConst = true;
    for (size_t i=0; i < r.getNumChildren(); ++i) {
      Node ri = r[i];
      bool recurse = true;
      if (!ri.isConst()) {
        if (m->d_equalityEngine->hasTerm(ri)) {
          TNode rir = m->d_equalityEngine->getRepresentative(ri);
          itMap = d_constantReps.find(rir);
          if (itMap != d_constantReps.end()) {
            if( (*itMap).second!=rir ){
              Trace("model-builder-debug") << "Bad constant rep : " << rir << " " << (*itMap).second << std::endl;
              Assert( false );
            }
            expl.push_back( ri.eqNode( (*itMap).second ) );
            ri = (*itMap).second;
            recurse = false;
          }
          else if (!evalOnly) {
            recurse = false;
          }
        }
        if (recurse) {
          ri = normalize(m, ri, evalOnly, expl);
        }
        if (!ri.isConst()) {
          childrenConst = false;
        }
      }
      children.push_back(ri);
    }
    retNode = NodeManager::currentNM()->mkNode( r.getKind(), children );
    if (childrenConst) {
      retNode = Rewriter::rewrite(retNode);
      Assert(retNode.getKind()==kind::APPLY_UF || retNode.getType().isRegExp() || retNode.isConst());
    }
  }
  d_normalizedCache[r] = retNode;
  //cache the explanation
  if( !expl.empty() ){
    Node exp;
    if( expl.size()>1 ){
      exp = NodeManager::currentNM()->mkNode( kind::AND, expl );
      expl.clear();
      expl.push_back( exp );
    }else{
      exp = expl[0];
    }
    d_normalizedCacheExp[r] = exp;
  }
  return retNode;
}

bool TheoryEngineModelBuilder::preProcessBuildModel(TheoryModel* m) {
  return true;
}

bool TheoryEngineModelBuilder::processBuildModel(TheoryModel* m){
  Trace("model-builder") << "Assigning function values..." << endl;
  //construct function values
  for( std::map< Node, std::vector< Node > >::iterator it = m->d_uf_terms.begin(); it != m->d_uf_terms.end(); ++it ){
    Node n = it->first;
    if( m->d_uf_models.find( n )==m->d_uf_models.end() ){
      TypeNode type = n.getType();
      Trace("model-builder") << "  Assign function value for " << n << " " << type << std::endl;
      uf::UfModelTree ufmt( n );
      Node default_v, un, simp, v;
      for( size_t i=0; i<it->second.size(); i++ ){
        un = it->second[i];
        vector<TNode> children;
        children.push_back(n);
        for (size_t j = 0; j < un.getNumChildren(); ++j) {
          children.push_back(m->getRepresentative(un[j]));
        }
        simp = NodeManager::currentNM()->mkNode(un.getKind(), children);
        v = m->getRepresentative(un);
        Trace("model-builder") << "  Setting (" << simp << ") to (" << v << "), from " << un << endl;
        ufmt.setValue(m, simp, v);
        default_v = v;
      }
      if( default_v.isNull() ){
        //choose default value from model if none exists
        TypeEnumerator te(type.getRangeType());
        default_v = (*te);
      }
      ufmt.setDefaultValue( m, default_v );
      if(options::condenseFunctionValues()) {
        ufmt.simplify();
      }
      Node val = ufmt.getFunctionValue( "_ufmt_", options::condenseFunctionValues() );
      Trace("model-builder") << "  Assigning (" << n << ") to (" << val << ")" << endl;
      m->d_uf_models[n] = val;
      //ufmt.debugPrint( std::cout, m );
    }
  }
  return true;
}

} /* namespace CVC4::theory */
} /* namespace CVC4 */
