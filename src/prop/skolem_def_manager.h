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

#include "expr/node.h"

namespace CVC4 {
namespace prop {

/**
 * This class manages the mapping between literals, the skolem they contain,
 * and the definitions for the skolems.
 */
class SkolemDefManager
{
 public:
  SkolemDefManager();

  ~SkolemDefManager();

  /** Notify skolem definitions */
  void notifySkolemDefinitions(const std::vector<Node>& skolems,
                               const std::vector<Node>& defs);
  /** Get activated definitions */
  void getActivatedDefinitions(TNode literal, std::vector<Node>& defs);

 private:
};

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__SKOLEM_DEF_MANAGER_H */
