# cvc5 Compile-Time Speedup — Working Log

**Branch:** `speedup-compile`
**Goal:** Meaningfully reduce cvc5 compile time (target: ~50%) without changing
build semantics (still a usable debug build: assertions, tracing, statistics on).
**Measurement command:** full rebuild with `make -j8`.

---

## Environment

> **Machine switch (2026-06-24):** Work moved from the original 8-core box to a
> bigger shared-home machine. All numbers below are from the **current** machine.

- Compiler: `g++ (GCC) 11.5.0` (`/usr/bin/c++`)
- Cores: **112**; RAM: 503 GB. Memory/parallelism are NOT constraints.
  - **Headline metric stays `make -j8`** (per request) so improvements in *total
    compile work* show clearly rather than being hidden by 112-way parallelism.
- Linkers present: `mold` (`~/.local/bin/mold`) and `ld.gold`.
  - ⚠️ GCC 11.5 here does **not** accept `-fuse-ld=mold` (that needs gcc ≥ 12).
    cvc5's CMake mold-probe fails and correctly falls back to **`-fuse-ld=gold`**.
    So on this machine the linker is **gold**, and a faster linker is not an
    easily-available lever (gold is already fast; link is a small fraction).
  - (The stale `build/` carried over via NFS home had `-fuse-ld=mold` baked in
    from the other machine → link errors. Fixed by a fresh reconfigure here.)
- `ccache`: **not installed**. Helps *re*builds, not a single clean build.
- Build config under test: **debug** (`./configure.sh debug --auto-download`)
  - From `cmake/ConfigDebug.cmake`: `-DCVC5_DEBUG`, `-fno-inline`,
    `OPTIMIZATION_LEVEL=g` (`-Og`), debug symbols ON (`-ggdb3 -gz`),
    statistics ON, assertions ON, proofs ON, tracing ON, **unit testing ON**.
  - Unit testing ON pulls in `test/` (206 `.cpp` files) on top of `src/`.

## Codebase scale

- `src/`: **791** `.cpp` files. Largest dirs:
  - `theory/quantifiers` (64 + `sygus` 45 + `ematching` 18 …)
  - `expr` (56), `theory` (55), `util` (38), `theory/strings` (38),
    `smt` (38), `preprocessing/passes` (36), `proof` (32).
- `test/`: 206 `.cpp` files.
- Build dir `build/` already has all external deps compiled under `build/deps`
  (GMP, CaDiCaL, poly, …). Deps are built once via ExternalProject and are NOT
  the recompilation pain — cvc5's own ~1000 TUs are. **We measure rebuilds of
  cvc5's own sources, with deps kept intact.**

## Current CMake state (relevant findings)

From top-level `CMakeLists.txt`:
- C++17, visibility hidden (default visibility in debug for unit tests).
- mold/gold linker auto-selected (lines ~295-324). Already optimal.
- IPO/LTO off by default (good — LTO would slow compiles).
- **No precompiled headers (PCH)** anywhere. ← big opportunity.
- **No unity/jumbo build** (`CMAKE_UNITY_BUILD`). ← biggest potential lever.
- `-gz` (compress debug sections) is on in debug → costs compile CPU.

---

## Plan of attack (ordered by expected ROI / safety)

1. **Baseline** — clean full `make -j8`, timed. *(IN PROGRESS — not yet captured)*
2. **Precompiled headers (PCH)** on the main `cvc5` library (and parser) for the
   heavy, ubiquitously-included headers (`expr/node.h`, `expr/kind.h`, common
   STL). Semantics-preserving. Typical 15-40% win on projects like this.
3. **Unity build** (`CMAKE_UNITY_BUILD` with a tuned batch size), applied
   per-library and tuned. Highest potential (often 2-3x) but riskiest
   (anonymous-namespace / macro / static collisions). Will trial on one library
   first, expand if clean.
4. **Trim redundant / heavy includes** in the hottest headers (guided by
   `-ftime-report` / include frequency). Slow, surgical, lower ROI — do after 2-3.
5. **Cheap flag wins** — e.g. drop `-gz` debug-section compression, consider
   `-g1` for the debug-symbol level. These change debug-info richness, so only
   with the user's OK; measure separately.
6. **ccache** (if installable) — helps incremental/repeat builds, not a single
   clean build. Document only.

### Measurement protocol
- Use the existing `build/` dir (deps already built; reconfigure picks up
  CMakeLists edits). To force a faithful from-scratch compile of cvc5 *without*
  rebuilding external deps: delete cvc5 object files (or `make clean`, after
  verifying it leaves `build/deps/**` intact) then `time make -j8`.
- Record wall-clock (and user+sys) for each configuration in the table below.
- For quick directional checks, build a single target (e.g. the core lib) rather
  than the whole tree; headline numbers are always full `make -j8`.

---

## Results table

All times: delete cvc5's own `*.o`/PCH under `build/{src,test}` (deps kept), then
`time make -j8`. Script: `measure.sh`.

| # | Configuration | Wall time (`make -j8`) | vs baseline | Notes |
|---|---------------|------------------------|-------------|-------|
| 0 | Baseline (debug, as-is) | **262.8 s** | — | full build: lib+bin+parser+unit tests |
| 1 | + PCH on `cvc5-obj` | **208.9 s** | **−20.5%** | `src/cvc5_pch.h` (node.h & core, C++ only). Dropped `rational.h` (latent `operator<<` ambiguity). Tests/parser not yet covered. |
| 2 | + Unity build (batch 8) + PCH | **109.2 s** | **−58.4%** | `UNITY_BUILD` on `cvc5-obj`. Required: add include guards to 2 unguarded headers; exclude vendored MiniSat from unity. Binary verified sat/unsat correct. |

### Unity batch-size sweep (`make -j8`, full build)

| batch | with PCH | **without PCH** | vs baseline (no PCH) |
|-------|----------|-----------------|----------------------|
| 8   | 109.2 s | — | |
| 16  | 89.1 s | 89.6 s | −65.9% |
| 32  | 74.6 s | 74.6 s | −71.6% |
| 64  | 71.1 s | **70.0 s** | **−73.4%** ← best for j8 |
| 128 | (fails*) | 73.8 s | −71.9% (too few TUs to fill 8 cores) |

\* 128 needs the generated `node_manager.cpp` excluded from unity (explicit
`mkConst<T>` specializations clash if the template is instantiated earlier in the
batch). Fixed by excluding it; also makes batch 64 robust to file reordering.

**Findings:**
- With unity at batch ≥16, **PCH adds nothing** (even ~1 s worse) — unity already
  parses each header once per batch, and the `.gch` load is pure overhead across
  the few remaining TUs. So *unity ⇒ disable PCH*.
- Best `-j8` clean build: **unity batch 64, no PCH = 70.0 s (−73.4%)**.
- Larger batches (128) regress at `-j8`: ~6 TUs can't saturate 8 cores.

### Incremental-build cost (the usual objection to unity) — measured

Full build once, then `touch` one file, then `make -j8 cvc5`:

| Edited file | PCH-only | unity-32 |
|-------------|----------|----------|
| heavy `theory/arith/theory_arith.cpp` | 27.3 s | 23.8 s |
| tiny `util/utility.cpp` | 24.1 s | **9.5 s** |

Counter-intuitive but explained: **relinking `libcvc5.so` dominates an
incremental rebuild**, not the single-file compile. Unity emits far fewer, larger
objects with much less duplicated debug info, so the *link* is dramatically
cheaper. Net: unity is faster for incremental builds too — the classic "unity
hurts iteration" objection does **not** apply here. (Editing a PCH header still
rebuilds everything in either mode.)

---

## TL;DR — result & how to use

**Full `make` rebuild of cvc5 cut by ~71%** (debug build, lib+bin+parser):

| | `make -j8` | `make -j32` |
|---|---|---|
| Baseline | 262.8 s | 93.9 s |
| **Now (default)** | **75.0 s** | **38.6 s** |
| Reduction | **−71.5%** | **−58.9%** |

Achieved with two CMake-level changes on the core library target `cvc5-obj`,
plus two small correctness fixes. **No source logic changed; build is still a
normal debug build** (assertions/tracing/statistics on) and is verified correct
(118/120 regression problems, 0 mismatches; `sat`/`unsat` smoke tests).

> **Note (2026-07-08):** the precompiled-header (PCH) mechanism was **removed** —
> unity is the sole speedup now. PCH was only ever a fallback for when unity is
> off, it added nothing under unity, and keeping one code path is simpler.
> Historical PCH numbers are left in the tables below as a record. `ENABLE_PCH`
> and `src/cvc5_pch.h` no longer exist.

**Defaults now:** unity build ON (batch 32). A plain `./configure.sh debug`
already gets the speedup. Tuning:
- Fastest clean `-j8` build: `-DUNITY_BATCH_SIZE=64` (70.0 s, −73.4%).
- Disable unity (e.g. to match upstream exactly, or to bisect a unity-only
  build issue): `./configure.sh debug -DENABLE_UNITY_BUILD=OFF`.
- All knobs go through `configure.sh`'s `-DVAR=VALUE` passthrough.

**What changed (all on branch `speedup-compile`):**
- `src/CMakeLists.txt`: `ENABLE_UNITY_BUILD` (default ON, batch 32) on
  `cvc5-obj`. Files carved out of unity batching (each for a concrete reason):
  vendored MiniSat, generated `node_manager.cpp`, generated `main/options.cpp`
  (static-build dup symbols), optional SAT wrappers `prop/kissat.cpp` &
  `prop/cryptominisat.cpp`, and — only under `USE_COCOA` — the CoCoA/finite-field
  sources. See "Multi-configuration validation" for why each is needed.
- `src/theory/uf/eq_proof.h`, `src/expr/type_checker_util.h`: added missing
  include guards (latent bug; also required for unity).
- **Validated across `debug`, `production`, `production --static`, and
  `--gpl --cocoa --cln --kissat`** — all compile and run correctly; ~68–72%
  faster in every config. (Helpers: `build-configs.sh`, `measure-dir.sh`.)

---

## Multi-configuration validation (2026-07-08)

The unity/PCH changes only touch the core library target `cvc5-obj`. The real
risk surface is configurations that (a) compile a **different set of source
files** into that target, or (b) **link it statically** (unity changes archive
extraction). Tested the main suspects, each in its own build dir with
`--auto-download` (`build-configs.sh`, paired timings via `measure-dir.sh`).

> ⚠️ Times here are on the **8-core** machine (gold linker), so absolute numbers
> differ from the 112-core numbers in the TL;DR above. What matters is the
> **paired unity-ON vs unity-OFF delta measured on the same box**. Every config
> stays ~68–72% faster and, after the fixes below, compiles and runs correctly.

| Config | Compiles | Binary | unity ON | unity OFF | **Δ** | PCH-only |
|--------|:---:|:---:|---:|---:|:---:|---:|
| `debug` (default) | ✅ | sat/unsat ✅ | 135.1 s | 476.7 s | **−71.7%** | 388.2 s (−18.6%) |
| `production` (`-O3`, NDEBUG) | ✅ | sat/unsat ✅ | 132.9 s | 423.6 s | **−68.6%** | 329.5 s (−22.2%) |
| `production --static` (static cvc5 libs) | ✅ *(after fix)* | sat/unsat ✅, fully static-linked | — | — | — | — |
| `debug --gpl --cocoa --cln --kissat` | ✅ *(after 2 fixes)* | sat/unsat/QF_FF ✅ | 146.7 s | 508.3 s | **−71.1%** | 406.1 s (−20.1%) |
| `production --static --static-binary` | ⛔ env | — | — | — | — | — |

`--static-binary` (fully static, incl. **system** libs) can't complete on this
machine: `libc.a` / `libstdc++.a` are not installed (no `glibc-static` /
`libstdc++-static` RPMs). This fails identically on stock `main` (unity OFF), so
it is **environmental, not caused by our change.** The `--static` row above still
exercises the important part — `libcvc5.a` static archive linking — end to end.
(CryptoMiniSat was dropped from the GPL config for the same reason: building its
*own* CLI links `libstdc++` statically and hits the same missing-lib wall; its
cvc5 wrapper is excluded from unity anyway.)

**Three real bugs were found and fixed by this multi-config testing** — all were
invisible to the original shared-debug-only validation:
1. `main/options.cpp` duplicate symbols in **static** builds (below).
2. CoCoA / finite-field unity collisions (`--cocoa`).
3. Optional SAT-backend wrapper unity collisions (`--kissat` / `--cryptominisat`).

### Bug 1 — `main/options.cpp` duplicate symbols in static builds (`cea3fabde0`)

`--static` builds failed to link with `multiple definition of
cvc5::main::parse / printUsage / parseInternal / ...`. Root cause: the generated
`main/options.cpp` is compiled into **both** `cvc5-obj` (→ `libcvc5.a`) and the
separate `main` object library that is linked into the binary. Normally the
linker never pulls the `libcvc5.a` copy (archive members load on demand and its
symbols are already provided). **Unity bundling defeats that**: `options.cpp`
lands in a unity object that also holds symbols the binary *does* need, so the
whole object is extracted → duplicate symbols. Only surfaces in **static**
builds (shared builds resolve to the single `.so` copy), which is why the
original shared-build validation missed it. **Fix:** exclude `main/options.cpp`
from unity, mirroring the `node_manager.cpp` / MiniSat exclusions.

### Bug 2 — CoCoA / finite-field unity collisions, `--cocoa` (`71b6c4b5b9`)

`debug --gpl --cocoa …` failed to compile two unity batches:
- `theory/ff/multi_roots.cpp` etc. each define `template<class T> std::string
  ostring(const T&)` at file scope in the same `theory::ff` namespace →
  *redefinition* once concatenated.
- `lazard_evaluation.cpp` & friends rely on file-scoped `using namespace` / ADL
  for CoCoA operators; concatenation makes `std::gcd` vs `CoCoA::gcd` and
  `operator<<(ostream, vector<CoCoA::RingElem>)` *ambiguous*.

**Fix:** when `USE_COCOA` is on, keep the CoCoA-touching sources (all
`theory/ff/*.cpp`, the two nl-arith `coverings` CoCoA files, `theory_arith.cpp`,
`util/cocoa_globals.cpp`) out of unity. When CoCoA is off they are inert and stay
in unity, so the default build is unaffected.

### Bug 3 — optional SAT-backend wrapper collisions, `--kissat`/`--cryptominisat` (`71b6c4b5b9`)

`prop/kissat.cpp` and `prop/cryptominisat.cpp` each define
`toSatValue` / `toSatValueLit` in the *anonymous* namespace of the enclosing
`cvc5::internal::prop` scope. In a unity TU those merge into one anonymous
namespace (mutual redefinition), and they additionally clash with
`cadical::toSatValue` — `prop/cadical/cadical.cpp` does `using namespace cadical;`
at namespace scope, which **leaks** to every file concatenated after it, making
the call ambiguous. **Fix:** keep both optional wrappers out of unity (cadical,
the default backend, stays in).

**Lesson:** shared-debug-only validation was insufficient. Static linking has
different symbol-resolution semantics, and optional/GPL deps compile a different
set of source files into the unity batches — both must be in the test matrix.
The fix pattern is uniform: **carve unity-hostile files out with
`SKIP_UNITY_BUILD_INCLUSION`; the rest of the library keeps the speedup.**

---

## Profiling (what to attack)

Most-included project headers across `src/` (`#include` count) and their
preprocessed weight (lines after `cpp`, with debug flags):

| Header | #includes | preprocessed lines |
|--------|-----------|--------------------|
| `expr/node.h` | 451 | 73,645 |
| `smt/env_obj.h` / `smt/env.h` | 237 / 112 | (env.h) 77,564 |
| `theory/rewriter.h` | 190 | 75,116 |
| `util/rational.h` | 146 | — |
| `expr/skolem_manager.h` | 146 | — |
| `theory/theory.h` | 85 | 77,957 |
| `proof/proof.h` | 63 | 78,944 |

Takeaway: ~450 TUs each reparse ~73K+ lines of `node.h` & friends. This is the
redundant work PCH (and unity) eliminate. Main library target: **`cvc5-obj`**
(`src/CMakeLists.txt:1502`), an OBJECT library over `LIBCVC5_SRCS`.

## Progress log

- **2026-06-24** — Set up branch `speedup-compile`. Surveyed build system.
  Key findings: mold already in use (linking not a lever), no PCH, no unity
  build (both big opportunities), debug uses `-Og -fno-inline -gz`. Wrote this
  log. Baseline measurement was about to run when work paused to switch machines.
- **2026-06-24 (machine 2)** — Reconfigured fresh (`./configure.sh debug
  --auto-download`) — needed because the NFS-shared `build/` was configured on
  the old machine with `-fuse-ld=mold`, which GCC 11.5 here rejects. Verified the
  binary builds & links (gold). Wrote `measure.sh`. **Captured baseline #0 =
  262.8 s.** Profiled header include frequency/weight (table above).
- **2026-06-24 (cont.)** — Implemented & measured the two levers:
  1. **PCH** on `cvc5-obj` → 208.9 s (−20.5%). Had to drop `util/rational.h`
     from the PCH (latent ambiguous `operator<<` exposed by early inclusion) and
     restrict the PCH to C++ (the target has a C source).
  2. **Unity build** on `cvc5-obj` → swept batch sizes; best `-j8` is batch 64
     (70.0 s, −73.4%); shipped default batch 32 (75.0 s, −71.5%) as a balance.
     Fixed unity blockers: 2 missing include guards, vendored MiniSat statics,
     generated `node_manager.cpp` `mkConst<T>` specializations.
  - Discovered unity *also* speeds incremental rebuilds (link of `libcvc5.so`,
    dominated by duplicated debug info, shrinks a lot) — so it's a win for both
    clean and incremental. PCH is redundant under unity → auto-skipped.
  - Verified correctness: 118/120 regress0 problems pass, 0 mismatches.
  - **Goal (−50%) exceeded: −71.5% at `-j8`, −58.9% at `-j32`.**
- **2026-07-08 (8-core machine)** — Multi-configuration validation (see section
  above). Built `debug`, `production`, `production --static`, and
  `debug --gpl --cocoa --cln --kissat`, each in its own `--auto-download` build
  dir, with paired unity-ON/OFF timings. **Found & fixed 3 real bugs** that the
  original shared-debug-only run never exercised: static-build duplicate symbols
  (`main/options.cpp`), CoCoA/finite-field unity collisions, and optional
  SAT-wrapper unity collisions. After the fixes every config compiles, runs
  (`sat`/`unsat`, plus `QF_FF` for the CoCoA build), and is 68–72% faster.
  `--static-binary` (fully static incl. system libs) is blocked by missing
  `libc.a`/`libstdc++.a` on this box — environmental, fails on stock `main` too.
  Commits `cea3fabde0`, `71b6c4b5b9`.
- **2026-07-08 (cont.)** — Removed the PCH mechanism (`ENABLE_PCH` option +
  `src/cvc5_pch.h`). Unity is now the only speedup path: PCH was pure fallback,
  contributed nothing when unity is on, and dropping it removes a code path and a
  maintained header. Verified `build/` still reconfigures and builds clean.

### Possible further levers (not pursued — diminishing returns past −71%)
- **Debug-info weight**: `-gz` (compress) + `-ggdb3` make objects large and the
  link slow. Dropping `-gz` or using `-g1` would speed compile+link further, but
  changes debug richness — a config choice, left to the user.
- **IWYU / redundant-include trimming** in hot headers: unity already removes the
  *repeated-parse* cost this would target, so ROI is now low. The 2 include-guard
  additions are the only include-hygiene fixes that were actually needed.
- **ccache**: not installed; would help repeated/CI rebuilds, orthogonal to this.
- **Extend unity/PCH to the parser and (EXCLUDE_FROM_ALL) unit tests**: not part
  of `make all`, so they don't affect the headline metric; easy to add later.

### Notes / gotchas discovered
- Bash tool working dir doesn't persist reliably between calls — use absolute
  paths (`make -C /home/fast/zoharyo1/git/cvc5_1/build ...`) instead of `cd`.
- Don't rebuild deps: they live in `build/deps`, take a long time, and are
  orthogonal to the goal.
