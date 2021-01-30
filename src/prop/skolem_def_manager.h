/*********************                                                        */
/*! \file skolem_def_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Skolem definition manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP__SKOLEM_DEF_MANAGER_H
#define CVC4__PROP__SKOLEM_DEF_MANAGER_H

#include <iosfwd>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/context.h"
#include "expr/node.h"

namespace CVC4 {

class RemoveTermFormulas;

namespace prop {

/**
 * This class manages the mapping between literals, the skolem they contain,
 * and the definitions for the skolems.
 */
class SkolemDefManager
{
 public:
  SkolemDefManager(context::Context* context,
                   context::UserContext* userContext,
                   RemoveTermFormulas& rtf);

  ~SkolemDefManager();

  /** Notify skolem definitions */
  void notifySkolemDefinitions(const std::vector<Node>& skolems,
                               const std::vector<Node>& defs);
  /** Get activated definitions */
  void getActivatedDefinitions(TNode literal, std::vector<Node>& defs);

 private:
  /** Reference to term formula removal */
  RemoveTermFormulas& d_rtf;
  /** skolems to definitions (user-context dependent) */
  /** set of active skolems (SAT-context dependent) */
};

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__SKOLEM_DEF_MANAGER_H */
