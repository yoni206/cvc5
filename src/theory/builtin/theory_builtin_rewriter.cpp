/*********************                                                        */
/*! \file theory_builtin_rewriter.cpp
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

#include "expr/attribute.h"
#include "theory/builtin/theory_builtin_rewriter.h"

#include "expr/chain.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace builtin {

namespace attr {
  struct LambdaBoundVarListTag { };
}/* CVC4::theory::arrays::attr namespace */

typedef expr::Attribute<attr::LambdaBoundVarListTag, Node> LambdaBoundVarListAttr;

Node TheoryBuiltinRewriter::blastDistinct(TNode in) {

  Assert(in.getKind() == kind::DISTINCT);

  if(in.getNumChildren() == 2) {
    // if this is the case exactly 1 != pair will be generated so the
    // AND is not required
    Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, in[0], in[1]);
    Node neq = NodeManager::currentNM()->mkNode(kind::NOT, eq);
    return neq;
  }

  // assume that in.getNumChildren() > 2 => diseqs.size() > 1
  vector<Node> diseqs;
  for(TNode::iterator i = in.begin(); i != in.end(); ++i) {
    TNode::iterator j = i;
    while(++j != in.end()) {
      Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, *i, *j);
      Node neq = NodeManager::currentNM()->mkNode(kind::NOT, eq);
      diseqs.push_back(neq);
    }
  }
  Node out = NodeManager::currentNM()->mkNode(kind::AND, diseqs);
  return out;
}

Node TheoryBuiltinRewriter::blastChain(TNode in) {

  Assert(in.getKind() == kind::CHAIN);

  Kind chainedOp = in.getOperator().getConst<Chain>().getOperator();

  if(in.getNumChildren() == 2) {
    // if this is the case exactly 1 pair will be generated so the
    // AND is not required
    return NodeManager::currentNM()->mkNode(chainedOp, in[0], in[1]);
  } else {
    NodeBuilder<> conj(kind::AND);
    for(TNode::iterator i = in.begin(), j = i + 1; j != in.end(); ++i, ++j) {
      conj << NodeManager::currentNM()->mkNode(chainedOp, *i, *j);
    }
    return conj;
  }
}



Node TheoryBuiltinRewriter::getLambdaForArrayRepresentationRec( TNode a, TNode bvl, unsigned bvlIndex, 
                                                                std::map< TNode, Node >& visited ){
  std::map< TNode, Node >::iterator it = visited.find( a );
  if( it==visited.end() ){
    Node ret;
    if( bvlIndex<bvl.getNumChildren() ){
      Assert( a.getType().isArray() );
      if( a.getKind()==kind::STORE ){
        // convert the array recursively
        Node body = getLambdaForArrayRepresentationRec( a[0], bvl, bvlIndex, visited );
        if( !body.isNull() ){
          // convert the value
          Node val = getLambdaForArrayRepresentationRec( a[2], bvl, bvlIndex+1, visited );
          if( !val.isNull() ){
            Assert( !TypeNode::leastCommonTypeNode( a[1].getType(), bvl[bvlIndex].getType() ).isNull() );
            Assert( !TypeNode::leastCommonTypeNode( val.getType(), body.getType() ).isNull() );
            //must orient the equality based on rewriter
            Node cond = Rewriter::rewrite( bvl[bvlIndex].eqNode( a[1] ) );
            ret = NodeManager::currentNM()->mkNode( kind::ITE, cond, val, body );
          }
        }
      }else if( a.getKind()==kind::STORE_ALL ){
        ArrayStoreAll storeAll = a.getConst<ArrayStoreAll>();
        Node sa = Node::fromExpr(storeAll.getExpr());
        ret = getLambdaForArrayRepresentationRec( sa, bvl, bvlIndex+1, visited );
      }
    }else{
      ret = a;
    }
    visited[a] = ret;
    return ret;
  }else{
    return it->second;
  }
}

Node TheoryBuiltinRewriter::getLambdaForArrayRepresentation( TNode a, TNode bvl ){
  Assert( a.getType().isArray() );
  std::map< TNode, Node > visited;
  Trace("builtin-rewrite-debug") << "Get lambda for : " << a << ", with variables " << bvl << std::endl;
  Node body = getLambdaForArrayRepresentationRec( a, bvl, 0, visited );
  if( !body.isNull() ){
    Trace("builtin-rewrite-debug") << "...got lambda body " << body << std::endl;
    return NodeManager::currentNM()->mkNode( kind::LAMBDA, bvl, body );
  }else{
    Trace("builtin-rewrite-debug") << "...failed to get lambda body" << std::endl;
    return Node::null();
  }
}

Node TheoryBuiltinRewriter::getArrayRepresentationForLambda( TNode n, bool reqConst ){
  Assert( n.getKind()==kind::LAMBDA );
  Trace("builtin-rewrite-debug") << "Get array representation for : " << n << std::endl;

  Node first_arg = n[0][0];
  Node rec_bvl;
  if( n[0].getNumChildren()>1 ){
    std::vector< Node > args;
    for( unsigned i=1; i<n[0].getNumChildren(); i++ ){
      args.push_back( n[0][i] );
    }
    rec_bvl = NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, args );
  }

  Trace("builtin-rewrite-debug2") << "  process body..." << std::endl;
  TypeNode retType;
  std::vector< Node > conds;
  std::vector< Node > vals;
  Node curr = n[1];
  while( curr.getKind()==kind::ITE ){
    Trace("builtin-rewrite-debug2") << "  process condition : " << curr[0] << std::endl;
    if( curr[0].getKind()!=kind::EQUAL ){
      // non-equality condition
      Trace("builtin-rewrite-debug2") << "  ...non-equality condition." << std::endl;
      return Node::null();
    }else if( Rewriter::rewrite( curr[0] )!=curr[0] ){
      // equality must be oriented correctly based on rewriter
      Trace("builtin-rewrite-debug2") << "  ...equality not oriented properly." << std::endl;
      return Node::null();
    }else{
      Node curr_index;
      for( unsigned r=0; r<2; r++ ){
        Node arg = curr[0][r];
        Node val = curr[0][1-r];
        if( arg==first_arg ){
          if( reqConst && !val.isConst() ){
            // non-constant value
            Trace("builtin-rewrite-debug2") << "  ...non-constant value." << std::endl;
            return Node::null();
          }else{
            curr_index = val;
            Trace("builtin-rewrite-debug2") << "    " << arg << " -> " << val << std::endl;
            break;
          }
        }
      }
      if( !curr_index.isNull() ){
        Node curr_val = curr[1];
        if( !rec_bvl.isNull() ){
          curr_val = NodeManager::currentNM()->mkNode( kind::LAMBDA, rec_bvl, curr_val );
          curr_val = getArrayRepresentationForLambda( curr_val, reqConst );
          if( curr_val.isNull() ){
            Trace("builtin-rewrite-debug2") << "  ...non-constant value." << std::endl;
            return Node::null();
          }
        }      
        Trace("builtin-rewrite-debug2") << "  ...condition is index " << curr_val << std::endl;
        conds.push_back( curr_index );
        vals.push_back( curr_val );
        TypeNode vtype = curr_val.getType();
        retType = retType.isNull() ? vtype : TypeNode::leastCommonTypeNode( retType, vtype );
      }else{
        Trace("builtin-rewrite-debug2") << "  ...non-constant value." << std::endl;
        return Node::null();
      }
      //recurse
      curr = curr[2];
    }
  }
  if( !rec_bvl.isNull() ){
    curr = NodeManager::currentNM()->mkNode( kind::LAMBDA, rec_bvl, curr );
    curr = getArrayRepresentationForLambda( curr );
  }
  if( !curr.isNull() && curr.isConst() ){
    TypeNode ctype = curr.getType();
    retType = retType.isNull() ? ctype : TypeNode::leastCommonTypeNode( retType, ctype );
    TypeNode array_type = NodeManager::currentNM()->mkArrayType( first_arg.getType(), retType );
    curr = NodeManager::currentNM()->mkConst(ArrayStoreAll(((ArrayType)array_type.toType()), curr.toExpr()));
    Trace("builtin-rewrite-debug2") << "  build array..." << std::endl;
    // can only build if default value is constant (since array store all must be constant)
    Trace("builtin-rewrite-debug2") << "  got constant base " << curr << std::endl;
    // construct store chain
    for( int i=((int)conds.size()-1); i>=0; i-- ){
      Assert( conds[i].getType().isSubtypeOf( first_arg.getType() ) );
      curr = NodeManager::currentNM()->mkNode( kind::STORE, curr, conds[i], vals[i] );
    }
    Trace("builtin-rewrite-debug") << "...got array " << curr << " for " << n << std::endl;
    return curr;
  }else{
    Trace("builtin-rewrite-debug") << "...failed to get array (cannot get constant default value)" << std::endl;
    return Node::null();    
  }
}

TypeNode TheoryBuiltinRewriter::getTruncatedArrayType( TypeNode tn, unsigned nargs ) {
  if( nargs==0 ){
    // dummy type : this is to prevent functions with array return type to be considered as arguments
    return NodeManager::currentNM()->integerType();
  }else{
    Assert( tn.isArray() );
    TypeNode tnt = getTruncatedArrayType( tn.getArrayConstituentType(), nargs-1 );
    return NodeManager::currentNM()->mkArrayType( tn.getArrayIndexType(), tnt );
  }
}

Node TheoryBuiltinRewriter::getLambdaBoundVarListForType( TypeNode tn, unsigned nargs ) {
  Trace("builtin-rewrite-debug") << "Truncate " << tn << " to [" << nargs << "]" << std::endl;
  Assert( tn.isArray() );
  TypeNode tnt = getTruncatedArrayType( tn, nargs );
  Trace("builtin-rewrite-debug") << "...got truncated type : " << tnt << std::endl;
  Node bvl = tnt.getAttribute(LambdaBoundVarListAttr());
  if( bvl.isNull() ){
    std::vector< TypeNode > types;
    TypeNode tnc = tnt;
    while( tnc.isArray() ){
      types.push_back( tnc.getArrayIndexType() );
      tnc = tnc.getArrayConstituentType();
    }
    std::vector< Node > vars;
    for( unsigned i=0; i<types.size(); i++ ){
      vars.push_back( NodeManager::currentNM()->mkBoundVar( types[i] ) );
    }
    bvl = NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, vars );
    Trace("builtin-rewrite-debug") << "Make standard bound var list " << bvl << " for " << tnt << std::endl;
    tnt.setAttribute(LambdaBoundVarListAttr(),bvl);
  }
  Assert( bvl.getNumChildren()==nargs );
  return bvl;
}

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
