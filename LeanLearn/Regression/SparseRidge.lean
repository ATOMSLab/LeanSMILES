/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanLearn.Scalar

/-!
# Ridge regression on sparse `0/1` features

Regression of a continuous target on sparse `0/1` features (a sample is the
list of its on-bits, as a Morgan fingerprint is) with scikit-learn's
`Ridge(alpha)` objective: a weight per bit and an intercept that is not
penalized,

    minimize  Σᵢ (yᵢ − w · xᵢ − b)² + α ‖w‖².

Centering removes the intercept: with `x̄`, `ȳ` the training means and
`X_c = X − 1 x̄ᵀ`, the weights solve `(X_cᵀ X_c + α I) w = X_cᵀ (y − ȳ)` and
`b = ȳ − x̄ · w`. That system is symmetric positive definite (α > 0), so
conjugate gradients solve it; each step needs only products with the sparse
`X` (about 40 of 2048 bits per molecule), with the centering applied on the
fly rather than by forming the dense `X_c`.

Hao Liu's `RidgeFloat` solves the same objective by Householder QR on a dense
design; this solver is for many sparse features (2048 fingerprint bits), where a
dense factorization is the expensive part. Fit quality is measured with
`LeanLearn/Regression/Metrics.lean`; `Pipelines/Tests/Ridge.lean` runs it on
Delaney's log solubility against scikit-learn.

Written over `ScalarLike` (`LeanLearn/Scalar.lean`), like the logistic model.
-/

@[expose] public section

namespace LeanLearn.Regression.SparseRidge

variable {K : Type} [ScalarLike K]

structure Model (K : Type) where
  weights : Array K
  bias : K

/-- Predicted value w · x + b. -/
def Model.predict (m : Model K) (x : Array ℕ) : K :=
  x.foldl (fun s j ↦ s + m.weights.getD j 0) m.bias

structure Config (K : Type) [ScalarLike K] where
  /-- Penalty strength, as scikit-learn's `alpha`. -/
  alpha : K := 1
  maxIter : ℕ := 10000
  /-- Stop when the residual norm falls below this fraction of the right-hand side's. -/
  tol : K := 0.000000000001

/-- Dot product of dense vectors. -/
def dot (u v : Array K) : K := (u.zip v).foldl (fun s (a, b) ↦ s + a * b) 0

/-- Train a ridge model on samples with `nFeatures` 0/1 features and targets.
Returns the model and the number of conjugate-gradient steps used. -/
def fit (cfg : Config K) (nFeatures : ℕ) (data : Array (Array ℕ × K)) :
    Model K × ℕ := Id.run do
  let count : K := data.foldl (fun s _ ↦ s + 1) 0
  let ybar := data.foldl (fun s (_, y) ↦ s + y) 0 / count
  -- feature means x̄
  let mut xbar : Array K := Array.replicate nFeatures 0
  for (x, _) in data do
    for j in x do
      xbar := xbar.modify j (· + 1)
  xbar := xbar.map (· / count)
  -- A v = X_cᵀ X_c v + α v, with X_c v = X v − (x̄ · v) 1
  let apply (v : Array K) : Array K := Id.run do
    let shift := dot xbar v
    let mut out : Array K := v.map (cfg.alpha * ·)
    let mut total : K := 0
    for (x, _) in data do
      let u := x.foldl (fun s j ↦ s + v.getD j 0) 0 - shift
      total := total + u
      for j in x do
        out := out.modify j (· + u)
    -- subtract x̄ (Σ u), the centering of X_cᵀ
    return (out.zip xbar).map fun (o, m) ↦ o - m * total
  -- right-hand side X_cᵀ (y − ȳ) = Xᵀ (y − ȳ), since Σ (y − ȳ) = 0
  let mut rhs : Array K := Array.replicate nFeatures 0
  for (x, y) in data do
    for j in x do
      rhs := rhs.modify j (· + (y - ybar))
  -- conjugate gradients from w = 0
  let mut w : Array K := Array.replicate nFeatures 0
  let mut r := rhs
  let mut p := rhs
  let mut rs := dot r r
  let stop := cfg.tol * cfg.tol * dot rhs rhs
  let mut iters := cfg.maxIter
  for k in [0:cfg.maxIter] do
    if rs ≤ stop then
      iters := k
      break
    let ap := apply p
    let step := rs / dot p ap
    w := (w.zip p).map fun (a, b) ↦ a + step * b
    r := (r.zip ap).map fun (a, b) ↦ a - step * b
    let rsNew := dot r r
    p := (r.zip p).map fun (a, b) ↦ a + (rsNew / rs) * b
    rs := rsNew
  return ({ weights := w, bias := ybar - dot xbar w }, iters)

end LeanLearn.Regression.SparseRidge
