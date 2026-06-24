/******************************************************************************
 * Precompiled-header payload for the cvc5 core library (cvc5-obj).
 *
 * This header is *only* used as the precompiled header for the main library
 * (see target_precompile_headers in src/CMakeLists.txt). It must contain only
 * stable, very widely included, expensive-to-parse headers. Every translation
 * unit in the library implicitly includes it first, so it is parsed once into a
 * PCH instead of ~hundreds of times.
 *
 * Do NOT add headers that change frequently (every edit here rebuilds the whole
 * library) or headers with translation-unit-specific behavior.
 *****************************************************************************/

#ifndef CVC5__CVC5_PCH_H
#define CVC5__CVC5_PCH_H

// --- Ubiquitous standard library headers (parsed in almost every TU) --------
#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <iosfwd>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

// --- cvc5 core headers (each pulls a large, stable transitive closure) ------
// expr/node.h is included by ~450 of the library's source files and drags in
// ~73k preprocessed lines (kind.h, type_node.h, metakind, ...). The others are
// the next most-included heavy headers.
#include "base/check.h"
#include "base/output.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/skolem_manager.h"
#include "expr/type_node.h"
#include "smt/env_obj.h"
#include "theory/rewriter.h"
// NOTE: util/rational.h deliberately NOT precompiled — including it first
// exposes a latent ambiguous operator<< (ManagedOut << std::string) in some
// options TUs. It is cheaper than node.h anyway, so little is lost.

#endif /* CVC5__CVC5_PCH_H */
