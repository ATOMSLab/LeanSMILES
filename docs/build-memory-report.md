# testing-df: build, compile and memory check (2026-10-21)

Branch `origin/testing-df` @ `3ff660f`, toolchain `leanprover/lean4:v4.30.0-rc1` (Lake 5.0.0),
Mathlib `v4.30.0-rc1` (`0c154d6`), warm Mathlib cache (7887 oleans, all 1987 Mathlib jobs
reported up-to-date before the build). Machine: 10-core Apple Silicon, 16 GB RAM, macOS.
Every Lean run below was serialised (`LEAN_NUM_THREADS=1`) so that per-process memory could be
measured; a sampler recorded the resident size of every Lean/Lake/clang process every 2 s.

## 1. Does the branch build? Yes.

`lake build` (default target `LeanSMILES`): **2662 jobs, 0 errors, 0 warnings, 6 min 32 s wall,
313 s of Lean elaboration** across the 51 project modules. No native compilation happened
(no `clang` invocation, no `.o`/`.dylib`; every module's `setup.json` has `dynlibs: []`).

Elaboration time per module (seconds, `lake build -v`):

| module | s | | module | s |
|---|---:|---|---|---:|
| Examples.CertifiedPipeline | **126** | | Proofs.ML.Convergence | 6.1 |
| Optimization.SmoothStrongConvexBridge | 26 | | Optimization.GDLinearConvergence | 6.1 |
| LearningTheory.Stability.Core | 14 | | LearningTheory...RidgeRegression1D.Minimizer | 6.1 |
| Real.Scalar | 13 | | Proofs.ML.LeastSquares | 5.7 |
| Proofs.LinSolve | 11 | | Proofs.LinAlg | 5.4 |
| LearningTheory...RidgeRegression1D.Real | 10 | | Optimization.StronglyConvexGD | 5.1 |
| Proofs.ML.Perceptron | 9.8 | | Proofs.Pipeline | 4.9 |
| Proofs.Chem.Distance | 7.2 | | everything else | ≤ 4.7 each |
| Proofs.Certificates | 6.5 | | all 25 `Polymorphic/` + `Float/` modules | ≤ 3.3 each |

The solver files themselves are not the problem: `Polymorphic/LinAlg.lean` (Gauss–Jordan,
`linSolve`) elaborates in 3 s at 0.6 GB; its correctness proof `Proofs/LinSolve.lean` in 11 s at
1.5 GB; `Proofs/ML/LeastSquares.lean` (normal equations via `linSolve`) in 6 s at 1.4 GB.

## 2. Memory per Lean process (max resident set, `/usr/bin/time -l`, one process at a time)

| what | peak RSS | wall |
|---|---:|---:|
| imports only (`Proofs.Certificates` + `Float.Pipeline`, i.e. the Mathlib closure these files need) | 2.4 GB* | — |
| `Real/Scalar.lean` (the ℝ instance; essentially imports + a small file) | 1.25 GB | 13 s |
| typical `Proofs/*`, `Optimization/*`, `LearningTheory/*` module | 1.3–1.5 GB | 5–26 s |
| `Proofs/LinSolve.lean` | 1.47 GB | 11 s |
| any `Polymorphic/*` or `Float/*` module (no Mathlib) | 0.63 GB | 2–3 s |
| **`Examples/CertifiedPipeline.lean`** | **2.3–2.4 GB** | **126–182 s** |
| &nbsp;&nbsp;of which: the two `decide +kernel` certificate checks alone | 2.7 GB | 17 s |
| &nbsp;&nbsp;of which: the two `#eval`s (gradient descent at `Float`) alone | 2.2 GB | 172 s |

\* the imports-only number is dominated by mmapped oleans and is an upper bound; the proof
modules that use those same imports settle at 1.3–1.5 GB.

So a single Lean process on this branch needs **about 1.5 GB, with one outlier at ~2.5 GB**.

### What that means for a parallel build

Lake 5 has no `-j`; it runs as many Lean processes as `LEAN_NUM_THREADS` (default: one per
core). Rough peak = cores × 1.5 GB (+1 GB for the outlier):

| machine | default build | with `LEAN_NUM_THREADS=4` (the repo's `.vscode/settings.json`) |
|---|---|---|
| 8-core, 8 GB laptop | ~13 GB → heavy swapping / OOM | ~7 GB → swapping |
| 10-core, 16 GB (this Mac) | ~16 GB → swapping | ~7 GB → fine |
| 8-core, 16 GB | ~13 GB → marginal | ~7 GB → fine |

The `.vscode/settings.json` cap only applies to the VS Code server. A command-line
`lake build` on a laptop should be run as `LEAN_NUM_THREADS=2 lake build` (or 4 on 16 GB).

## 3. The two real problems found

### 3a. `CertifiedPipeline.lean` runs 2–3 minutes of interpreted gradient descent every time it is elaborated

The `#eval`s train the ESOL pipeline (41 000 iterations on 1024-bit fingerprints) and the
graph pipeline (5000 iterations). They run in Lean's interpreter, not native code: **172 s of
the file's ~180 s**, every `lake build`, and every time the file is opened or edited in VS Code
(the server re-elaborates it, holding ~2.4 GB while it does). The kernel `decide` checks are
fine (17 s).

### 3b. `precompileModules = true` is dead configuration, and building `LeanSMILESExec` is a trap

`lakefile.toml` declares `LeanSMILESExec` (Polymorphic + Float, `precompileModules = true`)
*before* `LeanSMILES`. Lake resolves a module to a library with `findSomeRev?`, i.e. the
**last** declared library wins, and the `LeanSMILES` library keeps Lake's default
`roots = ["LeanSMILES"]`, which claims every module under `LeanSMILES.*`. Consequence
(verified in Lake's source, `Lake/Config/LeanLibConfig.lean` `isBuildableModule`, and in every
`setup.json`): no module is ever a member of `LeanSMILESExec`, nothing is precompiled, and
the README's "`#eval` runs at compiled speed" does not happen. That is why 3a is slow.

Worse: if anyone runs `lake build LeanSMILESExec` (the natural thing to try), Lake collects the
Exec modules, sees their imports as members of the *other* library, and tries to link
`libLeanSMILES.dylib` — which requires natively compiling **every module of that library and
its whole transitive closure, i.e. all of Mathlib** (~16 500 jobs, `clang` on each with one
process per core), and then fails with `error: build cycle detected`. I triggered this by
accident with a `lake query`; in three minutes it had compiled 3 800 Mathlib C files before I
killed it. Native objects dated 12:48–17:03 today in the shared Mathlib cache show at least one
other checkout on this Mac has been down the same path. On a laptop this looks exactly like
"compilation and memory issues around the solvers".

### The one-line fix

```toml
[[lean_lib]]
name = "LeanSMILES"
roots = []          # <- add: stop this library from claiming LeanSMILES.Polymorphic.* / Float.*
globs = [ ... ]
```

With it (checked with `lake build --no-build`, which plans without building):
`lake build LeanSMILESExec` becomes 70 jobs (the 25 Exec modules → `.o` → per-module dynlibs),
and the default `lake build` becomes 2163 jobs including those dynlibs, loaded when `Proofs/`
and `Examples/` are elaborated.

### Tested: a full build with the fix applied

Same serial settings, same machine (now under heavier load from other sessions):
**2709 jobs, 0 errors, 0 warnings, 5 min 17 s wall** (vs 6 min 32 s without the fix). Lake
compiled the 25 Exec modules to native code (47 `clang` invocations, each **≤ 0.15 s**; 23
per-module dylibs plus `libLeanSMILES_LeanSMILESExec.dylib`, linked in 0.1 s) — native
compilation is not a memory factor at all here. `CertifiedPipeline` was elaborated with the
shared library loaded (`setup.json` now lists it) and took **52 s instead of 126 s**; the
`#eval`s print the same numbers (`(0.000000, -1.451122)`, `(0.000000, -0.519829)`). What is
left of those 52 s is the kernel `decide` checks and Mathlib imports, plus swap noise.
(A separate `lake lean CertifiedPipeline.lean` run immediately afterwards took 152 s at 3.1 GB,
but it ran while this Mac had 11 Lean processes from other sessions and 42 GB of swap in use,
so I don't trust that number either way.)

This PR applies that change.

## 4. Caveats

* Timings in §2 marked with a range were taken while other sessions on this Mac were running up
  to 16 Lean processes (swap grew from 9 GB to 42 GB during the measurement); peak-RSS numbers
  are unaffected, wall times are upper bounds. The §1 build ran while the machine was quieter.
* No build was run at default parallelism on purpose; §2's parallel estimate is arithmetic.
* The Mathlib native objects my stray query wrote into the shared cache were deleted; the 623
  older ones from other checkouts were left in place.
