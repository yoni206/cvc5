/*********************                                                        */
/*! \file model_postprocessor.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include "smt/model_postprocessor.h"
#include "smt/boolean_terms.h"
#include "expr/node_manager_attributes.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::smt;

Node ModelPostprocessor::rewriteAs(TNode n, TypeNode asType) {
  if(n.getType().isSubtypeOf(asType)) {
    // good to go, we have the right type
    return n;
  }
  if(n.getKind() == kind::LAMBDA) {
    Assert(asType.isFunction());
    Node rhs = rewriteAs(n[1], asType[1]);
    Node out = NodeManager::currentNM()->mkNode(kind::LAMBDA, n[0], rhs);
    Debug("boolean-terms") << "rewrote " << n << " as " << out << std::endl;
    Debug("boolean-terms") << "need type " << asType << endl;
    // Assert(out.getType() == asType);
    return out;
  }
  if(!n.isConst()) {
    // we don't handle non-const right now
    return n;
  }
  if(n.getType().isRecord() && asType.isRecord()) {
    Debug("boolean-terms") << "+++ got a record - rewriteAs " << n << " : " << asType << endl;
    const Record& rec CVC4_UNUSED = n.getType().getConst<Record>();
    const Record& asRec = asType.getConst<Record>();
    Assert(rec.getNumFields() == asRec.getNumFields());
    Assert(n.getNumChildren() == asRec.getNumFields());
    NodeBuilder<> b(n.getKind());
    b << asType;
    for(size_t i = 0; i < n.getNumChildren(); ++i) {
      b << rewriteAs(n[i], TypeNode::fromType(asRec[i].second));
    }
    Node out = b;
    Debug("boolean-terms") << "+++ returning record " << out << endl;
    return out;
  }
  Debug("boolean-terms") << "+++ rewriteAs " << n << " : " << asType << endl;
  if(n.getType().isArray()) {
    Assert(asType.isArray());
    if(n.getKind() == kind::STORE) {
      return NodeManager::currentNM()->mkNode(kind::STORE,
                                              rewriteAs(n[0], asType),
                                              rewriteAs(n[1], asType[0]),
                                              rewriteAs(n[2], asType[1]));
    }
    Assert(n.getKind() == kind::STORE_ALL);
    const ArrayStoreAll& asa = n.getConst<ArrayStoreAll>();
    Node val = rewriteAs(asa.getExpr(), asType[1]);
    return NodeManager::currentNM()->mkConst(ArrayStoreAll(asType.toType(), val.toExpr()));
  }
  if(n.getType().isParametricDatatype() &&
     n.getType().isInstantiatedDatatype() &&
     asType.isParametricDatatype() &&
     asType.isInstantiatedDatatype() &&
     n.getType()[0] == asType[0]) {
    // Here, we're doing something like rewriting a (Pair BV1 BV1) as a
    // (Pair Bool Bool).
    const Datatype* dt2 = &asType[0].getDatatype();
    std::vector<TypeNode> fromParams, toParams;
    for(unsigned i = 0; i < dt2->getNumParameters(); ++i) {
      fromParams.push_back(TypeNode::fromType(dt2->getParameter(i)));
      toParams.push_back(asType[i + 1]);
    }
    Assert(dt2 == &Datatype::datatypeOf(n.getOperator().toExpr()));
    size_t ctor_ix = Datatype::indexOf(n.getOperator().toExpr());
    NodeBuilder<> appctorb(kind::APPLY_CONSTRUCTOR);
    appctorb << (*dt2)[ctor_ix].getConstructor();
    for(size_t j = 0; j < n.getNumChildren(); ++j) {
      TypeNode asType = TypeNode::fromType(SelectorType((*dt2)[ctor_ix][j].getSelector().getType()).getRangeType());
      asType = asType.substitute(fromParams.begin(), fromParams.end(), toParams.begin(), toParams.end());
      appctorb << rewriteAs(n[j], asType);
    }
    Node out = appctorb;
    return out;
  }
  if(asType.getNumChildren() != n.getNumChildren() ||
     n.getMetaKind() == kind::metakind::CONSTANT) {
    return n;
  }
  NodeBuilder<> b(n.getKind());
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
    b << n.getOperator();
  }
  TypeNode::iterator t = asType.begin();
  for(TNode::iterator i = n.begin(); i != n.end(); ++i, ++t) {
    Assert(t != asType.end());
    b << rewriteAs(*i, *t);
  }
  Assert(t == asType.end());
  Debug("boolean-terms") << "+++ constructing " << b << endl;
  Node out = b;
  return out;
}

void ModelPostprocessor::visit(TNode current, TNode parent) {
  Debug("tuprec") << "visiting " << current << endl;
  Assert(!alreadyVisited(current, TNode::null()));
  if(current.getType().hasAttribute(expr::DatatypeTupleAttr())) {
    Assert(current.getKind() == kind::APPLY_CONSTRUCTOR);
    TypeNode expectType = current.getType().getAttribute(expr::DatatypeTupleAttr());
    NodeBuilder<> b(kind::TUPLE);
    TypeNode::iterator t = expectType.begin();
    for(TNode::iterator i = current.begin(); i != current.end(); ++i, ++t) {
      Assert(alreadyVisited(*i, TNode::null()));
      Assert(t != expectType.end());
      TNode n = d_nodes[*i];
      n = n.isNull() ? *i : n;
      Assert( n.getType().isSubtypeOf(*t) );
      b << n;
    }
    Assert(t == expectType.end());
    d_nodes[current] = b;
    Debug("tuprec") << "returning " << d_nodes[current] << endl;
    // The assert below is too strong---we might be returning a model value but
    // expect a type that still uses datatypes for tuples/records.  If it's
    // really not the right type we should catch it in SmtEngine anyway.
    // Assert(d_nodes[current].getType() == expectType);
  } else if(current.getType().hasAttribute(expr::DatatypeRecordAttr())) {
    Assert(current.getKind() == kind::APPLY_CONSTRUCTOR);
    TypeNode expectType = current.getType().getAttribute(expr::DatatypeRecordAttr());
    const Record& expectRec = expectType.getConst<Record>();
    NodeBuilder<> b(kind::RECORD);
    b << current.getType().getAttribute(expr::DatatypeRecordAttr());
    Record::const_iterator t = expectRec.begin();
    for(TNode::iterator i = current.begin(); i != current.end(); ++i, ++t) {
      Assert(alreadyVisited(*i, TNode::null()));
      Assert(t != expectRec.end());
      TNode n = d_nodes[*i];
      n = n.isNull() ? *i : n;
      Assert(n.getType().isSubtypeOf(TypeNode::fromType((*t).second)));
      b << n;
    }
    Assert(t == expectRec.end());
    d_nodes[current] = b;
    Debug("tuprec") << "returning " << d_nodes[current] << endl;
    Assert(d_nodes[current].getType() == expectType);
  }else if(current.getKind() == kind::LAMBDA) {
    // rewrite based on children
    bool self = true;
    for(size_t i = 0; i < current.getNumChildren(); ++i) {
      Assert(d_nodes.find(current[i]) != d_nodes.end());
      if(!d_nodes[current[i]].isNull()) {
        self = false;
        break;
      }
    }
    if(self) {
      Debug("tuprec") << "returning self for kind " << current.getKind() << endl;
      // rewrite to self
      d_nodes[current] = Node::null();
    } else {
      // rewrite based on children
      NodeBuilder<> nb(current.getKind());
      if(current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        nb << current.getOperator();
      }
      for(size_t i = 0; i < current.getNumChildren(); ++i) {
        Assert(d_nodes.find(current[i]) != d_nodes.end());
        TNode rw = d_nodes[current[i]];
        if(rw.isNull()) {
          rw = current[i];
        }
        nb << rw;
      }
      d_nodes[current] = nb;
      Debug("tuprec") << "rewrote children for kind " << current.getKind() << " got " << d_nodes[current] << endl;
    }
  } else {
    Debug("tuprec") << "returning self for kind " << current.getKind() << endl;
    // rewrite to self
    d_nodes[current] = Node::null();
  }
}/* ModelPostprocessor::visit() */
