# LeanLearn

Learning algorithms on tabular data `(X, y)` and their proofs. The library imports Mathlib only
— no chemistry; the molecules are `LeanSMILES`'s, and `Pipelines/` is where the two meet.

Every executable algorithm is written once over the scalar interface of
[`Scalar.lean`](Scalar.lean): `Float` is what runs, `ℝ` is what the theorems are about, and the
polynomial fragment also runs exactly over `ℚ`. The layout follows that split:

| Folder | What it is |
|---|---|
| [`Regression/`](Regression) | executable linear regression, over any scalar: the ridge `Problem`, its iterative `Solvers` (gradient descent, Jacobi, Gauss–Seidel) and their exact `ℚ` `Certificates` (witnesses checked before a solver runs, and the residual check on whatever it produced); the `LinearModel` objectives on a Mathlib matrix; the Householder-QR solvers `OLSFloat` and `RidgeFloat`; `SparseRidge` (conjugate gradients on sparse 0/1 features), `SparseProblem` (the residual certificate on sparse 0/1 features, computed from the bit lists) and `Metrics` (R², RMSE, MAE) |
| [`Classification/`](Classification) | L2-regularized logistic regression on sparse 0/1 features (`Logistic`); ROC curves and AUC (`ROC`) |
| [`Plot/`](Plot) | parity plots as SVG |
| [`Proofs/LeastSquares/`](Proofs/LeastSquares) | over `ℝ`, on Mathlib matrices: ordinary least squares (`OLS`), diagonal ridge (`Ridge`), and the two against each other (`RidgeOLS`: the trade-off, shrinkage, the ridge path) |
| [`Proofs/Regression/`](Proofs/Regression) | over `ℝ`, about the executable code: the loss is an exact quadratic and any parameters are within `‖Aθ − b‖²/λ` of optimal (`Basic`), gradient descent's `O(1/k)` rate (`GradientDescent`), Jacobi and Gauss–Seidel under weighted diagonal dominance (`Iterative`), certificate soundness (`Certificates`), the sparse residual is the dense one (`SparseProblem`), and the bridges to the closed form (`MatrixBridge`: `Problem` is `Ridge` up to the factor `m`; `LinearModel`: the executable objectives are the specifications) |
| [`Examples/`](Examples) | `ols.lean`, `ridge.lean`: worked proofs on small exact designs; `olsFloat.lean`, `ridgeFloat.lean`: the `Float` solvers running |
| [`Tests/`](Tests) | `lake exe ols-float-test`, `ridge-float-test`, `linear-model-test` |

Executable files open `@[expose] public section`, so downstream code (and `decide +kernel`)
can unfold their definitions; theorem-only files open `public section`. The rest of this file
is the guide to the closed-form formulation; the iterative formulation and its certificates are
described in the repository README.

## Ordinary least squares and ridge regression

Author: Hao Liu

The algorithm-definition and proof part of linear regression. Its interface is
**a numerical feature matrix `X`, targets `y`, and coefficients `w`**; nothing
here assumes that a feature came from a SMILES string or a Morgan fingerprint.
Feature generation and training/evaluation belong to the calling pipeline
(`Pipelines/`). Solubility is one possible real-valued target; the theorems
apply equally to other numerical properties.

| File | Role |
|---|---|
| `Proofs/LeastSquares/OLS.lean` | Exact-real OLS definitions, inverse formula, optimality, uniqueness |
| `Proofs/LeastSquares/Ridge.lean` | Exact-real diagonal ridge definitions, optimality, positive-ridge existence and uniqueness |
| `Proofs/LeastSquares/RidgeOLS.lean` | Ridge against OLS: the shrinkage trade-off, ridge as a linear image of OLS, the ridge path's limits at `λ → 0` and `λ → ∞` |
| `Regression/LinearModel.lean` | Shared executable prediction/loss/stationarity definitions |
| `Proofs/Regression/LinearModel.lean` | Proofs connecting their real interpretation to OLS/ridge |
| `Proofs/Regression/MatrixBridge.lean` | The iterative `Problem` formulation (`Regression/Problem.lean`) is this problem up to the factor `m`: closed form and uniqueness transported, the shrinkage trade-off proved for it |
| `Regression/OLSFloat.lean` | Executable OLS on floating-point arrays using Householder QR |
| `Regression/RidgeFloat.lean` | Executable ridge regression using augmented Householder QR |
| `Examples/ols.lean`, `Examples/ridge.lean` | Exact, noisy, singular, exempt-intercept, duplicate-column and underdetermined examples proved in Lean |
| `Examples/olsFloat.lean`, `Examples/ridgeFloat.lean` | Runnable fitting and prediction demonstrations (`#eval`) |
| `Tests/OLSFloat.lean`, `Tests/RidgeFloat.lean` | Numerical regression and input-validation checks (`lake exe ols-float-test`, `ridge-float-test`) |
| `Tests/LinearModel.lean` | Float checks of the shared definitions on supplied coefficients (`lake exe linear-model-test`) |

The iterative solvers for the same problem (gradient descent, Jacobi,
Gauss–Seidel, written over the scalar interface with their certificates) are
`Problem.lean`, `Solvers.lean` and `Certificates.lean` in `Regression/`, by
DeMarko Fulcher; see the repository README.

- **The exact-real fitting definitions are noncomputable.** Use `Regression/OLSFloat.lean`
  and `Regression/RidgeFloat.lean` for executable Float fitting. Neither establishes
  floating-point rounding-error bounds.
- **Scalar convention.** Executable arithmetic is written with `PolynomialLike`,
  the polynomial fragment of `ScalarLike` (`Scalar.lean`); proofs
  specialize it to `ℝ`. `Float` is not assigned a lawful `Field` instance, which
  avoids assuming false identities such as associative floating-point addition.

### Input contract

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

For simple linear regression `y ≈ b + a x`, use two columns: a column of ones
for the intercept and a column containing `x`. The coefficient vector is then
`[b, a]`, in that order. For example:

```lean
import LeanLearn.Proofs.LeastSquares.OLS

open Matrix
open scoped Matrix

-- Three observations with x = 0, 1, 2.
def X : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 1, 1; 1, 2]
def y : Fin 3 → ℝ := ![1, 3, 5]
```

### Algorithms and guarantees

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

| OLS theorem | Meaning |
|---|---|
| `loss_eq_sum` | The dot-product definition equals the usual sum of squared errors |
| `loss_nonneg` | Squared-error loss cannot be negative |
| `normalEquations_iff` | The residual and Gram-matrix forms of the normal equations agree |
| `loss_add_of_normalEquations` | Perturbing a normal-equation solution by `d` adds exactly `‖Xd‖²` to its loss |
| `normalEquations_minimize` | Every normal-equation solution is a global minimizer, even when `XᵀX` is singular |
| `fit_normalEquations` | The closed-form solution satisfies the normal equations under the nonsingularity hypothesis |
| `fit_minimizes` | The coefficients returned by `fit` globally minimize the loss |
| `fit_unique` | Every global minimizer equals those coefficients under the same hypothesis |

The central proof expands the square:

```text
‖X(w + d) - y‖²
  = ‖Xw - y‖² + 2 (Xw - y)ᵀXd + ‖Xd‖²
  = ‖Xw - y‖² + ‖Xd‖².
```

The middle term vanishes because the normal equations make the residual
orthogonal to every feature column. The remaining extra term is nonnegative.

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

`RidgeOLS.lean` puts the two models side by side. Nothing below assumes a
rank condition unless it says so:

| Ridge-vs-OLS theorem | Meaning |
|---|---|
| `isMinimizer_zero_penalty` | At zero penalty the ridge minimizers are the OLS minimizers |
| `isMinimizer_iff_augmented` | For nonnegative weights, the ridge minimizers are the OLS minimizers on the augmented design `[X; diag √ρ]`, `[y; 0]` |
| `penalty_le_of_isMinimizer` | **The trade-off**: a ridge minimizer has no larger penalized norm `Σⱼ ρⱼ wⱼ²` than any OLS minimizer (and, by definition of the latter, no smaller squared error) |
| `penalty_antitone`, `ols_loss_monotone` | Along `λ ↦ λρ`, the minimizer's penalized norm falls and its squared error rises |
| `fit_eq_shrink_ols_fit` | `wρ = (XᵀX + diag ρ)⁻¹ XᵀX w₀`: ridge is a linear image of OLS |
| `fit_eq_smul_ols_fit_of_gram_eq_one` | Orthonormal columns: `wλ = w₀ / (1 + λ)` |
| `path`, `continuousOn_path` | The ridge path `λ ↦ (XᵀX + λI)⁻¹ Xᵀy` is continuous on `λ > 0` for every design |
| `tendsto_path_nhds_zero` | `wλ → w₀` as `λ → 0` when `XᵀX` is nonsingular |
| `sum_sq_le_of_isMinimizer`, `tendsto_sum_sq_path_atTop` | `‖wλ‖² ≤ ‖y‖² / λ`, so `‖wλ‖² → 0` as `λ → ∞` |

An exempt intercept means not all weights are positive, so the automatic
positive-ridge uniqueness theorem does not apply directly. General optimality
still holds for nonnegative weights. Uniqueness requires a separate regularized
Gram positive-definiteness argument; a zero unpenalized feature column, for
example, prevents uniqueness.

All global-optimality statements quantify over **every real coefficient
vector**, rather than a finite collection of candidates.

### Shared definitions and their proofs

`Regression/LinearModel.lean` provides `predictRow`, `predict`, `residual`, `squaredError`,
`penalty`, `ridgeLoss`, and `normalResidual`. They use `sumGen` over
`List.finRange`, which fixes an evaluation order and works with Float.

The bridge theorems (`Proofs/Regression/LinearModel.lean`) `predict_real`, `squaredError_real`, `ridgeLoss_real`, and
`normalResidual_eq_zero_iff` prove that the same definitions, interpreted at
`ℝ`, agree with the exact specifications. `ols_fit_minimizes`,
`stationary_minimizes`, and `ridge_fit_minimizes` express correctness directly
using these shared objective definitions.

For example, a downstream caller can compute predictions and losses:

```lean
import LeanLearn.Regression.LinearModel
open LeanLearn.Regression
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

### The iterative formulation is the same problem

`Regression/Problem.lean` (DeMarko Fulcher) writes ridge regression as the *averaged* loss
`L(θ) = (1/m) Σᵣ (⟪xᵣ, θ⟫ − yᵣ)² + λ ‖θ‖²` over executable `Vec`s, a constant
`1` appended to every sample for the intercept, with normal equations
`A θ = b` for the iterative solvers. `Proofs/Regression/MatrixBridge.lean`
proves, over `ℝ`, that this is the problem above up to the factor `m`: with
`X = P.designMatrix` (every sample with its `1`), `y = P.target` and `ρ = m λ`
on every coefficient,

```text
‖Xθ − y‖² + m λ ‖θ‖² = m · L(θ)         (every m)
XᵀX + m λ I = m · A,    Xᵀy = m · b      (m > 0)
```

so for `m > 0` the two formulations have the same normal equations and the
same minimizers, and the theorems above transfer to `Problem`:

| Bridge theorem | Meaning |
|---|---|
| `predict_designMatrix`, `residual_designMatrix` | `Xθ` is the vector of fitted values `⟪xᵣ, θ⟫`; `Xθ − y` the residuals |
| `ridge_loss_eq`, `loss_eq_ridge_loss` | `Ridge.loss X y (mλ) θ = m · P.loss θ`; for `m > 0`, `P.loss θ = (1/m) · Ridge.loss …` |
| `ols_loss_eq`, `mse_eq_ols_loss` | `OLS.loss X y θ = m · P.mse θ`, the mean squared error |
| `gram_apply`, `transpose_mulVec_target` | `XᵀX + mλI = m · A` and `Xᵀy = m · b`, entry by entry |
| `residual_eq_zero_iff_normalEquations` | `A θ = b` is exactly `Ridge.NormalEquations X y (mλ) θ` |
| `isMinimizer_iff` | `θ` minimizes `P.loss` iff it minimizes `Ridge.loss X y (mλ)` |
| `closedForm`, `closedForm_isMinimizer`, `isMinimizer_unique`, `existsUnique_isMinimizer` | For `λ > 0`, `(XᵀX + mλI)⁻¹ Xᵀy` is the unique minimizer of `P.loss`, for every design |
| `dot_self_le_of_isMinimizer` | A minimizer of `P` (`λ > 0`) has no larger `‖θ‖²` than any least-squares minimizer on the same data |
| `dot_self_antitone`, `mse_monotone` | Raising `λ` can only shrink the minimizer's `‖θ‖²` and raise its mean squared error (the ridge-vs-OLS trade-off, for every `m`) |

The averaging is the whole difference. It does not move the minimizers, but
it rescales the penalty — `Problem` with `λ` is `Ridge` with `ρ = mλ` — so a
`λ` tuned in one formulation is `mλ` in the other. At `m = 0` the loss
identity still holds (both sides are `0`), but `L(θ) = λ‖θ‖²` while the matrix
problem is empty, so the statements about normal equations and minimizers
assume `m > 0`.

### Run OLS on floating-point data

`OLSFloat.fit X y` accepts rows of numerical features and one target per row.
Include a column of ones in `X` to fit an intercept. The solver scales columns
and targets, performs Householder QR, and solves the resulting triangular
system; it does not form or invert `XᵀX`.

```lean
import LeanLearn.Regression.OLSFloat

open LeanLearn.Regression.OLSFloat

-- Rows are observations. The first column of ones supplies an intercept.
def X : Design := #[#[1.0, 0.0], #[1.0, 1.0], #[1.0, 2.0]]
def y : Array Float := #[1.0, 3.0, 5.0]

#eval do
  let model ← fit X y
  let prediction ← model.predict #[1.0, 3.0]
  pure (model.coefficients, prediction)
-- Approximately: Except.ok (#[1.0, 2.0], 7.0)
```

`Design` abbreviates `Array (Array Float)`. `fit` returns
`Except Error Model`: `.ok model` on success, or `.error reason` on failure.

| API | Result |
|---|---|
| `fit X y` | A model whose coefficient order matches the columns of `X` |
| `model.predict row` | One predicted target |
| `model.predictAll X` | An array of predicted targets |
| `model.sumSquaredError X y` | Sum of squared residuals, without averaging |

The solver checks dimensions, nonempty fitting data, finite inputs, and the
requirement that the number of observations is at least the number of columns.
The default `rankTolerance` is `1e-10`; it compares each column's remaining QR
norm with that column's original scaled norm (`fit X y { rankTolerance := 1e-8 }`).
Singular, underdetermined, and numerically rank-deficient designs return
errors; no pseudoinverse or regularized fallback is used. Non-finite numerical
results are also errors. Finite results remain subject to rounding, especially
on ill-conditioned data.

### Run ridge regression on floating-point data

`RidgeFloat.fit` minimizes `Σᵢ ((Xw)ᵢ - yᵢ)² + penalty * Σⱼ wⱼ²`. The default
penalty is `1.0`, and every supplied coefficient is penalized. Use
`unpenalizedColumn` to exempt an explicit intercept column:

```lean
import LeanLearn.Regression.RidgeFloat

open LeanLearn.Regression.RidgeFloat

def ridgeX : Design := #[#[1.0, 0.0], #[1.0, 1.0], #[1.0, 2.0]]
def ridgeY : Array Float := #[1.0, 3.0, 5.0]

#eval do
  let model ← fit ridgeX ridgeY { penalty := 2.0, unpenalizedColumn := some 0 }
  let prediction ← model.predict #[1.0, 3.0]
  let objective ← model.penalizedLoss ridgeX ridgeY
  pure (model.coefficients, prediction, objective)
-- Approximately: Except.ok (#[2.0, 1.0], 5.0, 4.0)
```

`penalty` must be finite and nonnegative. A positive penalty can make a
singular or underdetermined design identifiable; an exempt column must still
be independent of the penalized columns in the augmented design. At zero
penalty, the solver behaves like OLS and rejects underdetermined or
rank-deficient designs. The same relative `rankTolerance` check applies.

### Build and inspect

From the repository root:

```bash
lake build LeanLearn
lake exe ols-float-test
lake exe ridge-float-test
lake exe linear-model-test
```

A successful build of `Proofs/LeastSquares/` and `Proofs/Regression/LinearModel.lean` means
Lean has checked the proofs. Open the repository in a Lean-enabled editor and inspect
`Examples/ols.lean` and `ridge.lean` in the Infoview to follow the
worked proofs step by step; `olsFloat.lean` and `ridgeFloat.lean` show the Float
solvers running.

### Scope of the guarantee

Theorems about real arithmetic establish exact optimization properties. A
definition's availability at Float does not transfer those theorems to IEEE
arithmetic: rounding, NaN, overflow, and underflow require separate analysis.
Callers must supply finite numerical values and interpret Float outputs as
approximations. No Float conditioning bound or verified numerical solver is
claimed here. The Float QR implementation is tested on known solutions, scale
changes, and invalid inputs; no theorem yet connects its finite-precision output
to the exact-real solution or bounds its rounding error.

This folder makes no assertion about SMILES canonicalization, data quality,
Morgan invariance, optimizer convergence, train/test leakage, generalization,
or physical accuracy of a solubility prediction.
