# OLS and ridge: algorithm definitions and proofs

- **The OLS proofs in `Update` are not stronger than the original OLS proofs.**
  `OLS.lean` and `OLSExamples.lean` retain the same mathematical proofs, with
  namespace changes. The main additions are the ridge proofs and the shared
  scalar-generic definitions with theorems connecting their real interpretation
  to the OLS and ridge specifications.
- **`Update` is not a complete replacement for the numerical solvers.** Its
  exact-real fitting definitions are noncomputable, and its Float examples use
  supplied coefficients to calculate predictions and losses. Use the existing
  `OLSFloat.lean` and `RidgeFloat.lean` for executable Float fitting. Neither set
  establishes floating-point rounding-error bounds.

This directory contains the machine-learning algorithm formalization for
LeanSMILES. Its interface is **a numerical feature matrix `X`, targets `y`,
and coefficients `w`**. In the planned molecular-property pipeline:

```text
SMILES → canonical SMILES → cleaned data → Morgan features
                                              ↓
                                  X : n × p, y : n
                                              ↓
                           OLS / ridge specification and proofs
                                              ↓
                                  linear property prediction
```

Feature generation and experimental training/evaluation belong to the calling
pipeline. Nothing here assumes that a feature came from a SMILES string or a
Morgan fingerprint. Solubility is one possible real-valued target; the theorems
apply equally to other numerical properties.

## Relation to the `canonical-smiles` branch

Inspected branch: `canonical-smiles`, commit
`5b5fe9e6fd25011a38e803109ec8f61a970b2890` (2026-10-22 inspection).
The branch has canonicalization modules, Morgan fingerprints, the shared
`LeanSMILES.Scalar` arithmetic interface, and `LeanSMILES.ML.Logistic`.

This directory follows that branch's scalar convention: executable arithmetic
is written with `PolynomialLike`, the polynomial fragment of `ScalarLike`;
proofs specialize it to `ℝ`. `Float` is not assigned a lawful `Field` instance.
This avoids assuming false identities such as associative floating-point
addition. The local `Scalar.lean` was checked to match the branch's version.

The directory is independent of the older modules directly under
`Algorithms/`: its imports are Mathlib, `LeanSMILES.Scalar`, and modules within
`Algorithms/Update`. All declarations live under
`LeanSMILES.Algorithms.Update`, so the older and updated versions can coexist.
No branch switch or modification of chemistry/fingerprint modules is required.

## Files

| File | Role |
|---|---|
| `All.lean` | One import for all core definitions and proofs |
| `OLS.lean` | Exact-real OLS definitions, inverse formula, optimality, uniqueness |
| `Ridge.lean` | Exact-real diagonal ridge definitions, optimality, positive-ridge existence and uniqueness |
| `LinearModel.lean` | Shared executable prediction/loss/stationarity definitions and proofs connecting their real interpretation to OLS/ridge |
| `OLSExamples.lean` | Exact, noisy, and singular OLS examples proved in Lean |
| `RidgeExamples.lean` | Exempt-intercept, duplicate-column, and underdetermined ridge examples proved in Lean |
| `FloatExamples.lean` | Runnable Float predictions and objective checks with supplied coefficients |

## Input contract

```lean
X : Matrix (Fin n) (Fin p) K
y : Fin n → K
w : Fin p → K
```

Rows represent observations and columns represent features. `Fin` indices make
the dimensions part of the types. The feature order must remain the same for
prediction. Include an explicit column of ones for an intercept; its coefficient
is then an ordinary entry of `w`. No intercept or feature normalization is
inserted implicitly.

`K := Float` runs the shared definitions; `K := ℝ` is their proved mathematical
interpretation. The shared polynomial definitions also support `ℚ`.
The upstream team supplies its own conversion from fingerprints/arrays into
these dimension-indexed inputs.

## Algorithms and guarantees

OLS minimizes the unaveraged sum of squared errors:

```text
L(w) = Σᵢ ((Xw)ᵢ − yᵢ)²
normal equations: Xᵀ(Xw − y) = 0
exact fit: (XᵀX)⁻¹ Xᵀy
```

`OLS.fit` requires an explicit proof that `det(XᵀX) ≠ 0`.
`OLS.fit_normalEquations`, `OLS.fit_minimizes`, and `OLS.fit_unique` prove that
its output satisfies the normal equations and is the unique global minimizer.
`OLS.normalEquations_minimize` proves global optimality of any normal-equation
solution even when the design is singular. Singular OLS can have multiple
minimizers; no full-rank hypothesis is silently inferred from fingerprint data.

Ridge minimizes a diagonally weighted coefficient penalty:

```text
Lρ(w) = L(w) + Σⱼ ρⱼ wⱼ²
normal equations: (XᵀX + diag ρ)w = Xᵀy
exact fit: (XᵀX + diag ρ)⁻¹ Xᵀy
```

Use `ρ := fun _ => strength` for ordinary ridge. To exempt an intercept, set
its weight to zero. The penalty uses the original supplied feature units;
there is no implicit standardization or division by the observation count.

| Ridge theorem | Guarantee |
|---|---|
| `loss_nonneg` | Nonnegative weights imply nonnegative loss |
| `normalEquations_iff` | Gram and residual equations are equivalent |
| `loss_add_of_normalEquations` | Exact objective increase under any coefficient perturbation |
| `normalEquations_minimize` | Every solution is globally optimal for nonnegative weights |
| `fit_normalEquations`, `fit_minimizes` | Correctness of the inverse formula under nonsingularity |
| `gram_posDef`, `gram_det_ne_zero` | Strictly positive weights guarantee invertibility for every design |
| `fitPositive_minimizes`, `fitPositive_unique` | Positive ridge's exact fit is optimal and unique |
| `exists_unique_minimizer` | Positive ridge has a unique minimizer even for singular or underdetermined designs |
| `normalEquations_unique` | Uniqueness when the regularized Gram matrix is positive definite |
| `loss_zero_penalty`, `normalEquations_zero_penalty`, `fit_zero_penalty` | Exact reduction to OLS at zero penalty |
| `augmented_loss` | Ridge equals OLS on the square-root-penalty augmented design |

An exempt intercept means not all weights are positive, so the automatic
positive-ridge uniqueness theorem does not apply directly. General optimality
still holds for nonnegative weights. Uniqueness requires a separate regularized
Gram positive-definiteness argument; a zero unpenalized feature column, for
example, prevents uniqueness.

All global-optimality statements quantify over **every real coefficient
vector**, rather than a finite collection of candidates.

## Shared definitions and their proofs

`LinearModel` provides `predictRow`, `predict`, `residual`, `squaredError`,
`penalty`, `ridgeLoss`, and `normalResidual`. They use `sumGen` over
`List.finRange`, which fixes an evaluation order and works with Float.

The bridge theorems `predict_real`, `squaredError_real`, `ridgeLoss_real`, and
`normalResidual_eq_zero_iff` prove that the same definitions, interpreted at
`ℝ`, agree with the exact specifications. `ols_fit_minimizes`,
`stationary_minimizes`, and `ridge_fit_minimizes` express correctness directly
using these shared objective definitions.

For example, a downstream caller can compute predictions and losses:

```lean
import LeanSMILES.Algorithms.Update.All
open LeanSMILES.Algorithms.Update
open Matrix
open scoped Matrix

def X : LinearModel.Design Float 3 2 := !![1, 0; 1, 1; 1, 2]
def y : Fin 3 → Float := ![1, 3, 5]
def coefficients : Fin 2 → Float := ![2, 1]
def weights : Fin 2 → Float := ![0, 2]

#eval LinearModel.predictRow ![1, 3] coefficients  -- 5
#eval LinearModel.squaredError X y coefficients   -- 2
#eval LinearModel.ridgeLoss X y weights coefficients -- 4
```

For formal use, import `Update.All`, open the same namespace, supply real
`X`, `y`, and the stated hypotheses, and apply the OLS/ridge theorems. See the
two proved example files for complete concrete arguments.

## Build and inspect

Run from the repository root:

```bash
lake build LeanSMILES.Algorithms.Update.All \
  LeanSMILES.Algorithms.Update.OLSExamples \
  LeanSMILES.Algorithms.Update.RidgeExamples \
  LeanSMILES.Algorithms.Update.FloatExamples
lake env lean --run LeanSMILES/Algorithms/Update/FloatExamples.lean
```

Open the repository in a Lean-enabled editor and inspect `OLSExamples.lean`
and `RidgeExamples.lean` in Infoview. Building the proof files checks their
theorems; running `FloatExamples` checks eight numerical evaluations. The
examples do not train models or evaluate a property dataset.

## Scope of the proof

Theorems about real arithmetic establish exact optimization properties. A
definition's availability at Float does not transfer those theorems to IEEE
arithmetic: rounding, NaN, overflow, and underflow require separate analysis.
Callers must supply finite numerical values and interpret Float outputs as
approximations. No Float conditioning bound or verified numerical solver is
claimed here. The exact-real inverse definitions are noncomputable and are
not an executable Float fitting routine.

The previous certified-rational and Float-QR implementations remain in the
parent directory; they are not dependencies of this proof-focused update.
This folder makes no assertion about SMILES canonicalization, data quality,
Morgan invariance, optimizer convergence, train/test leakage, generalization,
or physical accuracy of a solubility prediction.
