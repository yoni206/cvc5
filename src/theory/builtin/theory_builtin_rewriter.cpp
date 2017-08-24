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



Node TheoryBuiltinRewriter::getLambdaForArrayRepresentationRec( Node a, Node bvl ){
  if( a.getKind()==kind::STORE ){
    Node body = getLambdaForArrayRepresentationRec( a[0], bvl );
    if( !body.isNull() ){
      Node cond;
      if( bvl.getNumChildren()>1 ){
        Assert( a[1].getType().isTuple() );
        Assert( a[1].getKind()==kind::APPLY_CONSTRUCTOR );
        Assert( a[1].getNumChildren()==bvl.getNumChildren() );
        std::vector< Node > conds;
        for( unsigned i=0; i<bvl.getNumChildren(); i++ ){
          Assert( a[1][i].getType()==bvl[i].getType() );
          //must orient the equality based on rewriter
          conds.push_back( Rewriter::rewrite( bvl[i].eqNode( a[1][i] ) ) );
        }
        cond = NodeManager::currentNM()->mkNode( kind::AND, conds );
      }else{
        //must orient the equality based on rewriter
        cond = Rewriter::rewrite( bvl[0].eqNode( a[1] ) );
      }
      return NodeManager::currentNM()->mkNode( kind::ITE, cond, a[2], body );
    }
  }else if( a.getKind()==kind::STORE_ALL ){
    ArrayStoreAll storeAll = a.getConst<ArrayStoreAll>();
    return Node::fromExpr(storeAll.getExpr());
  }
  return Node::null();
}

Node TheoryBuiltinRewriter::getLambdaForArrayRepresentation( Node a, Node bvl ){
  Assert( a.getType().isArray() );
  Trace("builtin-rewrite-debug") << "Get lambda for : " << a << ", with variables " << bvl << std::endl;
  Node body = getLambdaForArrayRepresentationRec( a, bvl );
  if( !body.isNull() ){
    Trace("builtin-rewrite-debug") << "...got lambda body" << body << std::endl;
    return NodeManager::currentNM()->mkNode( kind::LAMBDA, bvl, body );
  }else{
    Trace("builtin-rewrite-debug") << "...failed to get lambda body" << std::endl;
    return Node::null();
  }
}

Node TheoryBuiltinRewriter::getArrayRepresentationForLambda( Node n, bool allowPermute, bool reqConst ){
  Assert( n.getKind()==kind::LAMBDA );
  Trace("builtin-rewrite-debug") << "Get array representation for : " << n << std::endl;
  std::vector< Node > args;
  std::vector< TypeNode > arg_types;
  for( unsigned i=0; i<n[0].getNumChildren(); i++ ){
    args.push_back( n[0][i] );
    arg_types.push_back( n[0][i].getType() );
  }
  Trace("builtin-rewrite-debug2") << "  array arg types..." << std::endl;
  TypeNode arg_type;
  Node cv_cons;
  if( arg_types.size()>1 ){
    arg_type = NodeManager::currentNM()->mkTupleType( arg_types );
    cv_cons = Node::fromExpr( ((DatatypeType)arg_type.toType()).getDatatype()[0].getConstructor() );
  }else{
    arg_type = arg_types[0];    
  }
  Trace("builtin-rewrite-debug2") << "  making array type : " << arg_type << " " << n[1].getType() << "..." << std::endl;
  TypeNode array_type = NodeManager::currentNM()->mkArrayType( arg_type, n[1].getType() );
  
  Trace("builtin-rewrite-debug2") << "  process body..." << std::endl;
  std::vector< Node > conds;
  std::vector< Node > vals;
  Node curr = n[1];
  while( curr.getKind()==kind::ITE ){
    Trace("builtin-rewrite-debug2") << "  process condition : " << curr[0] << std::endl;
    std::vector< Node > curr_conds;
    if( curr[0].getKind()==kind::AND ){
      for( unsigned i=0; i<curr[0].getNumChildren(); i++ ){
        curr_conds.push_back( curr[0][i] );
      }      
    }else{  
      curr_conds.push_back( curr[0] );
    }
    if( curr_conds.size()!=args.size() ){
      return Node::null();
    }else{
      std::map< Node, Node > arg_to_val; 
      for( unsigned i=0; i<curr_conds.size(); i++ ){
        if( curr_conds[i].getKind()!=kind::EQUAL ){
          // non-equality condition
          Trace("builtin-rewrite-debug2") << "  ...non-equality condition." << std::endl;
          return Node::null();
        }else{
          if( !allowPermute ){
            // equality must be oriented correctly based on rewriter
            if( Rewriter::rewrite( curr_conds[i] )!=curr_conds[i] ){
              Trace("builtin-rewrite-debug2") << "  ...equality not oriented properly." << std::endl;
              return Node::null();
            }
          }
          for( unsigned r=0; r<2; r++ ){
            Node arg = curr_conds[i][r];
            Node val = curr_conds[i][1-r];
            bool success = true;
            if( allowPermute ){
              if( std::find( args.begin(), args.end(), arg )==args.end() ){
                // not an argument
                success = false;
              }else if( arg_to_val.find( arg )!=arg_to_val.end() ){
                // repeated arg
                Trace("builtin-rewrite-debug2") << "  ...repeated argument." << std::endl;
                return Node::null();
              }
            }else{  
              if( arg!=args[i] ){
                //out of order argument
                success = false;
              }
            }
            if( success ){
              if( reqConst && !val.isConst() ){
                // non-constant value
                Trace("builtin-rewrite-debug2") << "  ...non-constant value." << std::endl;
                return Node::null();
              }else{
                arg_to_val[arg] = val;
                Trace("builtin-rewrite-debug2") << "    " << arg << " -> " << val << std::endl;
                break;
              }
            }
          }
        }
      }
      Node cond_val;
      if( args.size()==1 ){
        Assert( arg_to_val.find( args[0] )!=arg_to_val.end() );
        cond_val = arg_to_val[args[0]];
      }else{
        std::vector< Node > cond_val_children;
        cond_val_children.push_back( cv_cons );
        for( unsigned i=0; i<args.size(); i++ ){
          Assert( arg_to_val.find( args[i] )!=arg_to_val.end() );
          cond_val_children.push_back( arg_to_val[args[i]] );
        }
        cond_val = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, cond_val_children );
      }
      Trace("builtin-rewrite-debug2") << "  ...condition is index " << cond_val << std::endl;
      conds.push_back( cond_val );
      vals.push_back( curr[1] );
      //recurse
      curr = curr[2];
    }
  }    
  if( curr.isConst() ){
    Trace("builtin-rewrite-debug2") << "  build array..." << std::endl;
    // can only build if default value is constant (since array store all must be constant)
    Node array_val = NodeManager::currentNM()->mkConst(ArrayStoreAll(((ArrayType)array_type.toType()),curr.toExpr()));
    Trace("builtin-rewrite-debug2") << "  got constant base " << array_val << std::endl;
    // construct store chain
    for( int i=((int)conds.size()-1); i>=0; i-- ){
      array_val = NodeManager::currentNM()->mkNode( kind::STORE, array_val, conds[i], vals[i] );
    }
    Trace("builtin-rewrite-debug") << "...got array " << array_val << std::endl;
    return array_val;
  }else{
    Trace("builtin-rewrite-debug") << "...failed to get array (default value not constant)" << std::endl;
    return Node::null();    
  }
}

Node TheoryBuiltinRewriter::getLambdaBoundVarListForType( TypeNode tn ) {
  Node bvl = tn.getAttribute(LambdaBoundVarListAttr());
  if( bvl.isNull() ){
    std::vector< TypeNode > types;
    if( tn.isTuple() ){
      types = tn.getTupleTypes();
    }else{
      types.push_back( tn );  
    }
    std::vector< Node > vars;
    for( unsigned i=0; i<types.size(); i++ ){
      vars.push_back( NodeManager::currentNM()->mkBoundVar( types[i] ) );
    }
    Assert( !vars.empty() );
    bvl = NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, vars );
    tn.setAttribute(LambdaBoundVarListAttr(),bvl);
  }
  return bvl;
}

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
