# Ordinary least squares and ridge regression in Lean

Author: Hao Liu

This folder starts the algorithm-definition and proof part of LeanSMILES.
It accepts numerical features and targets directly. Other modules can prepare
those features from molecules or other data sources.

## Files and how to check them

- `OLS.lean`: the mathematical definitions, closed-form solution, and general proofs.
- `OLSExamples.lean`: small worked examples proved with exact arithmetic.
- `OLSFloat.lean`: executable OLS on floating-point arrays using Householder QR.
- `OLSFloatExamples.lean`: a runnable fitting and prediction demonstration.
- `OLSFloatTests.lean`: numerical regression and input-validation checks.
- `RidgeFloat.lean`: executable ridge regression using augmented Householder QR.
- `RidgeFloatExamples.lean`: a runnable ridge fitting and prediction demonstration.
- `RidgeFloatTests.lean`: ridge numerical and input-validation checks.

From the repository root (the folder containing `lakefile.toml`):

```bash
lake build LeanSMILES.Algorithms.OLS LeanSMILES.Algorithms.OLSExamples
```

A successful build of `OLS.lean` and `OLSExamples.lean` means Lean has checked
the proofs. Those two files do not define an executable `main` function or run
a training/test dataset. Open the whole repository in VS Code, then open
`LeanSMILES/Algorithms/OLSExamples.lean` to inspect the proof steps in Lean's
Infoview.

## Run OLS on floating-point data

From the repository root:

```bash
lake build LeanSMILES.Algorithms.OLSFloat
lake env lean --run LeanSMILES/Algorithms/OLSFloatExamples.lean
lake env lean --run LeanSMILES/Algorithms/OLSFloatTests.lean
```

The example prints coefficients `[1, 2]`, a prediction of `7` at `x = 3`, and
approximately zero squared error. It also fits the noisy example and shows
how a singular design is rejected. Printed decimal values are rounded.

For your own inputs:

```lean
import LeanSMILES.Algorithms.OLSFloat

open LeanSMILES.Algorithms.OLSFloat

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
The `←` notation propagates an error instead of continuing with an invalid model.

| API | Result |
|---|---|
| `fit X y` | A model whose coefficient order matches the columns of `X` |
| `model.predict row` | One predicted target |
| `model.predictAll X` | An array of predicted targets |
| `model.sumSquaredError X y` | Sum of squared residuals, without averaging |

All four operations return checked `Except` results. No column is added
automatically: for an intercept include ones in both fitting and prediction
rows. Without that column, the model is fitted through the origin.

The solver checks dimensions, nonempty fitting data, finite inputs, and the
requirement that the number of observations is at least the number of columns.
It scales columns and targets, uses Householder QR, and back-substitutes to
obtain the coefficients. It does not explicitly form or invert `XᵀX`.

The default `rankTolerance` is `1e-10`. It compares each column's remaining QR
norm with that column's original scaled norm. You may set it explicitly:

```lean
#eval fit X y { rankTolerance := 1e-8 }
```

A larger tolerance rejects more nearly dependent designs. This check is a
numerical heuristic and can depend on column order. Singular, underdetermined,
and numerically rank-deficient designs return errors; no pseudoinverse or
regularized fallback is used. Non-finite numerical results are also errors.
Finite results remain subject to rounding, especially on ill-conditioned data.

## Run ridge regression on floating-point data

From the repository root:

```bash
lake build LeanSMILES.Algorithms.RidgeFloat
lake env lean --run LeanSMILES/Algorithms/RidgeFloatExamples.lean
lake env lean --run LeanSMILES/Algorithms/RidgeFloatTests.lean
```

`RidgeFloat.fit` minimizes
`Σᵢ ((Xw)ᵢ - yᵢ)² + penalty * Σⱼ wⱼ²`. The default penalty is `1.0`,
and every supplied coefficient is penalized. Use `unpenalizedColumn` to
exempt an explicit intercept column:

```lean
import LeanSMILES.Algorithms.RidgeFloat

open LeanSMILES.Algorithms.RidgeFloat

def ridgeX : Design := #[#[1.0, 0.0], #[1.0, 1.0], #[1.0, 2.0]]
def ridgeY : Array Float := #[1.0, 3.0, 5.0]

#eval do
  let model ← fit ridgeX ridgeY { penalty := 2.0, unpenalizedColumn := some 0 }
  let prediction ← model.predict #[1.0, 3.0]
  let objective ← model.penalizedLoss ridgeX ridgeY
  pure (model.coefficients, prediction, objective)
-- Approximately: Except.ok (#[2.0, 1.0], 5.0, 4.0)
```

The column index is zero-based. The output order matches the input columns.
`model.predict`, `model.predictAll`, and `model.sumSquaredError` have the
same checked behavior as their OLS Float counterparts. `model.penalizedLoss`
adds the configured penalty to the sum of squared errors.

`penalty` must be finite and nonnegative. A positive penalty can make a
singular or underdetermined design identifiable; an exempt column must still
be independent of the penalized columns in the augmented design. At zero
penalty, the solver behaves like OLS and rejects underdetermined or
rank-deficient designs. The solver scales the augmented design and uses
Householder QR without forming `XᵀX`. The same relative `rankTolerance`
check applies, so extreme scaling or a very small penalty can still trigger
a numerical rank error. These executable results have no formal rounding
error bound.

## Inputs and the model

For `n` observations and `p` coefficients:

| Lean type | Mathematical meaning |
|---|---|
| `X : Matrix (Fin n) (Fin p) ℝ` | Design matrix: rows are observations, columns are features |
| `y : Fin n → ℝ` | Observed target for each row |
| `w : Fin p → ℝ` | Model coefficients |

`Fin n` is the index type `0, …, n - 1`. These types ensure that the dimensions
match. Prediction is `Xw`; the residual is `Xw - y`.

For simple linear regression `y ≈ b + a x`, use two columns: a column of ones
for the intercept and a column containing `x`. The coefficient vector is then
`[b, a]`, in that order. For example:

```lean
import LeanSMILES.Algorithms.OLS

open Matrix
open scoped Matrix

-- Three observations with x = 0, 1, 2.
def X : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 1, 1; 1, 2]
def y : Fin 3 → ℝ := ![1, 3, 5]
```

An intercept is optional: the algorithm uses exactly the columns supplied.
There is no regularization, sample weighting, or iterative optimizer.

## Objective, algorithm, and guarantee

The loss is the sum of squared errors:

```text
loss(X, y, w) = Σᵢ ((Xw)ᵢ - yᵢ)²
```

`IsMinimizer X y w` means that this loss is no larger than the loss of **any**
other coefficient vector. This is a global optimum, not a check against a
finite collection of alternatives.

The normal equations are:

```text
Xᵀ (Xw - y) = 0       equivalently       (XᵀX)w = Xᵀy
```

`fit` defines the closed-form OLS solution:

```text
ŵ = (XᵀX)⁻¹ Xᵀy
```

To call it, supply a proof `h : (gram X).det ≠ 0`, where `gram X = XᵀX`:

```lean
-- Given X, y and h:
-- let coefficients := LeanSMILES.Algorithms.OLS.fit X y h
```

This nonsingularity condition ensures the coefficient vector is uniquely
identifiable. It is not inferred automatically from arbitrary supplied data.

## What the proofs establish

| Theorem | Meaning |
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
The inverse identities then prove that `fit` satisfies those equations and
that no different coefficient vector can achieve the same minimum.

## Worked examples

1. **Exact line:** `x = [0, 1, 2]`, `y = [1, 3, 5]`. The proved solution is
   intercept `1`, slope `2`, with loss `0`.
2. **Noisy line:** the same inputs, `y = [1, 2, 4]`. The proved solution is
   intercept `5/6`, slope `3/2`. Every coefficient vector has loss at least `1/6`.
3. **Singular design:** both columns are `[1, 1]`, with targets `[1, 3]`.
   Coefficients `[2, 0]` and `[0, 2]` are distinct global minimizers.
   The Gram determinant is zero, so `fit`'s precondition fails. The general
   normal-equation optimality theorem still applies.

## How to read a Lean proof

A `def` introduces an object or a mathematical definition. For example,
`loss` defines what squared error means, and `fit` defines the coefficient formula.
A `theorem` states a proposition and provides evidence that it follows from
its assumptions. The text after `:= by` constructs that evidence.

In `fit_minimizes`, the assumption is that `XᵀX` has nonzero determinant.
The conclusion says that the loss at `fit X y h` is no greater than the loss
at any other coefficient vector. The statement applies to every finite real
matrix and target vector satisfying the assumption, not just the three
worked examples.

Commands such as `rw`, `ring`, and `linarith` help construct a proof:
`rw` rewrites using a known equality, `ring` verifies polynomial identities,
and `linarith` derives consequences of linear equalities and inequalities.
Lean's kernel checks the proof they produce. Running `lake build` verifies
these logical statements; it does not measure predictive accuracy on new data.

The examples apply the general theorems to concrete matrices. They show both
how to use the results and why the nonsingularity assumption matters.

## Scope of the guarantee

The proofs concern exact real arithmetic (`ℝ`): for example, `1/3` denotes
exactly one third. A numerical program typically uses `Float`, whose finite
precision introduces rounding, so the stored value of one third is approximate.
A theorem about exact arithmetic does not by itself bound those rounding errors.

The definitions in `OLS.lean` use Lean's `noncomputable` real-number machinery.
Lean can reason about their coefficient formula and verify its theorems, but
those exact-real definitions are not directly executable with `#eval`.

`OLSFloat.lean` provides the executable numerical solver. It solves the same
unweighted OLS problem through QR, while the proof module expresses the exact
solution through the Gram-matrix inverse. The Float implementation is tested
on known solutions, scale changes, and invalid inputs. No theorem yet connects
its finite-precision output to the exact-real solution or bounds its rounding
error. Compiling the Float code checks its types; running its tests checks
specific numerical cases. Neither establishes a general numerical error bound.

The modules do not yet provide a pseudoinverse solver for singular designs,
prove existence of a minimizer for every singular design, or formally verify
the Float QR implementation. The exact-real optimality/uniqueness theorems
and the executable solver provide the starting points for that later work.
