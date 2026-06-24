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
  262.8 s.** Profiled header include frequency/weight (table above). **Next:** PCH
  on `cvc5-obj`.

### Notes / gotchas discovered
- Bash tool working dir doesn't persist reliably between calls — use absolute
  paths (`make -C /home/fast/zoharyo1/git/cvc5_1/build ...`) instead of `cd`.
- Don't rebuild deps: they live in `build/deps`, take a long time, and are
  orthogonal to the goal.
