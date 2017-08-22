/*********************                                                        */
/*! \file theory_uf_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__THEORY_UF_REWRITER_H
#define __CVC4__THEORY__UF__THEORY_UF_REWRITER_H

#include "theory/rewriter.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUfRewriter {

public:

  static RewriteResponse postRewrite(TNode node) {
    if(node.getKind() == kind::EQUAL) {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      } else if(node[0].isConst() && node[1].isConst()) {
        // uninterpreted constants are all distinct
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
      }
      if (node[0] > node[1]) {
        Node newNode = NodeManager::currentNM()->mkNode(node.getKind(), node[1], node[0]);
        return RewriteResponse(REWRITE_DONE, newNode);
      }
    }
    if(node.getKind() == kind::APPLY_UF && node.getOperator().getKind() == kind::LAMBDA) {
      // resolve away the lambda
      context::Context fakeContext;
      theory::SubstitutionMap substitutions(&fakeContext);
      TNode lambda = node.getOperator();
      for(TNode::iterator formal = lambda[0].begin(), arg = node.begin(); formal != lambda[0].end(); ++formal, ++arg) {
        // typechecking should ensure that the APPLY_UF is well-typed, correct arity, etc.
        Assert(formal != node.end());
        // This rewrite step is important: if we have (f (f 5)) for
        // some lambda term f, we want to beta-reduce the inside (f 5)
        // application first.  Otherwise, we can end up in infinite
        // recursion, because f's formal (say "x") gives the
        // substitution "x |-> (f 5)".  Fine, the body of the lambda
        // gets (f 5) in place for x.  But since the same lambda ("f")
        // now occurs in the body, it's got the same bound var "x", so
        // substitution continues and we replace that x by (f 5).  And
        // then again.  :-(
        //
        // We need a better solution for distinguishing bound
        // variables like this, but for now, handle it by going
        // inside-out.  (Quantifiers shouldn't ever have this problem,
        // so long as the bound vars in different quantifiers are kept
        // different.)
        Node n = Rewriter::rewrite(*arg);
        substitutions.addSubstitution(*formal, n);
      }
      return RewriteResponse(REWRITE_AGAIN_FULL, substitutions.apply(lambda[1]));
    }else if( node.getKind() == kind::HO_APPLY ){
      if( node[0].getKind() == kind::LAMBDA ){
        // resolve one argument of the lambda
        TNode arg = Rewriter::rewrite( node[1] );
        TNode var = node[0][0][0];
        Node new_body = node[0][1].substitute( var, arg );
        if( node[0][0].getNumChildren()>1 ){
          std::vector< Node > new_vars;
          for( unsigned i=1; i<node[0][0].getNumChildren(); i++ ){
            new_vars.push_back( node[0][0][i] );
          }
          std::vector< Node > largs;
          largs.push_back( NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, new_vars ) );
          largs.push_back( new_body );
          new_body = NodeManager::currentNM()->mkNode( kind::LAMBDA, largs );
        }
        return RewriteResponse( REWRITE_AGAIN_FULL, new_body );
      }else{
        //rewrite to APPLY_UF if full application of non-variable function
        if( node[0].getType().getNumChildren()==2 ){
          std::vector< Node > children;
          Node curr = node;
          while( curr.getKind() == kind::HO_APPLY ){
            children.push_back( node[1] );
            curr = node[0];        
          }
          if( node[0].getKind()!=kind::BOUND_VARIABLE ){
            children.push_back( node[0] );
            std::reverse( children.begin(), children.end() );
            Node ret = NodeManager::currentNM()->mkNode( kind::APPLY_UF, children );
            return RewriteResponse( REWRITE_AGAIN_FULL, ret );
          }
        }
      }
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  static RewriteResponse preRewrite(TNode node) {
    if(node.getKind() == kind::EQUAL) {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      } else if(node[0].isConst() && node[1].isConst()) {
        // uninterpreted constants are all distinct
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
      }
    }
    if(node.getKind() == kind::APPLY_UF && node.getOperator().getKind() == kind::LAMBDA) {
      // resolve away the lambda
      context::Context fakeContext;
      theory::SubstitutionMap substitutions(&fakeContext);
      TNode lambda = node.getOperator();
      for(TNode::iterator formal = lambda[0].begin(), arg = node.begin(); formal != lambda[0].end(); ++formal, ++arg) {
        // typechecking should ensure that the APPLY_UF is well-typed, correct arity, etc.
        Assert(formal != node.end());
        // This rewrite step is important: see note in postRewrite().
        Node n = Rewriter::rewrite(*arg);
        substitutions.addSubstitution(*formal, n);
      }
      return RewriteResponse(REWRITE_DONE, substitutions.apply(lambda[1]));
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline void init() {}
  static inline void shutdown() {}

};/* class TheoryUfRewriter */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_REWRITER_H */
