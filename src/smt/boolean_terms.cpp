/*********************                                                        */
/*! \file boolean_terms.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "smt/boolean_terms.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"
#include "theory/booleans/boolean_term_conversion_mode.h"
#include "theory/booleans/options.h"
#include "expr/kind.h"
#include "expr/node_manager_attributes.h"
#include "util/ntuple.h"
#include <string>
#include <algorithm>
#include <set>
#include <map>
#include <stack>

using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::booleans;

namespace CVC4 {
namespace smt {

}/* CVC4::smt namespace */
}/* CVC4 namespace */
