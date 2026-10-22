module

public import LeanSMILES.Polymorphic.ML.LinearModel
public import LeanSMILES.Polymorphic.ML.GradientDescent

/-!
# Machine Learning — Least squares

Linear regression: minimise the mean squared error over affine models, either in closed
form (`olsFit`) or by gradient descent (`linRegGD`, `linRegGDSparse`).
-/

@[expose] public section

namespace ML

open Primitives

/-! ## Linear Regression

Least squares: minimise `mse` over affine models. The bias is handled by appending a
column of ones (`augmentMat`) and solving for `θ = (w, b)` in the augmented space.
-/

section LinearRegression

variable {α : Type} [Scalar α] {m n : Nat}

/-- Residuals `rᵢ = score xᵢ - yᵢ`. -/
@[specialize] def residuals (model : LinearModel α n) (data : Dataset α m n) : Vec α m :=
  Vector.ofFn fun i => model.score data.X[i] - data.y[i]

/-- Mean squared error `(1/m) ∑ᵢ (score xᵢ - yᵢ)² = ‖r‖² / m`. -/
@[specialize] def mse (model : LinearModel α n) (data : Dataset α m n) : α :=
  normSq (residuals model data) / Scalar.fromNat m

/-- `(2/m) Xₐᵀ (Xₐ θ - y)` with `Xₐ` and `Xₐᵀ` supplied, so callers can compute them once. -/
@[specialize] def mseGradAux (Xa : Mat α m (n + 1)) (XaT : Mat α (n + 1) m) (y : Vec α m)
    (θ : Vec α (n + 1)) : Vec α (n + 1) :=
  smul (Scalar.fromNat 2 / Scalar.fromNat m) (matVec XaT (vsub (matVec Xa θ) y))

/-- Gradient of `θ ↦ mse (ofParams θ) data`: `(2/m) Xₐᵀ (Xₐ θ - y)`, where `Xₐ` is the
augmented design matrix. -/
@[specialize] def mseGrad (data : Dataset α m n) (θ : Vec α (n + 1)) : Vec α (n + 1) :=
  let Xa := augmentMat data.X
  mseGradAux Xa (transpose Xa) data.y θ

/-- The least-squares objective in parameter space, for `gradientDescent`. `Xₐ` and `Xₐᵀ`
are computed once, outside the gradient closure; `grad` is definitionally `mseGrad data`. -/
@[specialize] def mseObjective (data : Dataset α m n) : Objective α (n + 1) :=
  let Xa := augmentMat data.X
  let XaT := transpose Xa
  { loss := fun θ => mse (LinearModel.ofParams θ) data
    grad := mseGradAux Xa XaT data.y }

/-- Closed-form least squares: solve the normal equations `(XₐᵀXₐ) θ = Xₐᵀ y`.
Proved (over `ℝ`, `olsFit_optimal_of_fullColumnRank` in `Proofs/ML/LeastSquares.lean`):
when the augmented features are linearly independent, no linear model has a smaller
`mse`. -/
@[specialize] def olsFit (data : Dataset α m n) : LinearModel α n :=
  let Xa := augmentMat data.X
  LinearModel.ofParams (linSolve (gram Xa) (matVec (transpose Xa) data.y))

/-- Least squares by gradient descent on `mseObjective`, starting from `θ = 0`.
Proved (over `ℝ`, `Proofs/ML/`): with `0 ≤ η` and `η ∑ᵢ ‖xᵢ‖² ≤ m` the training `mse`
never increases (`mse_linRegGD_antitone`); a fixed point is a global minimiser
(`mse_le_of_gdStep_eq_self`); and with `2η ∑ᵢ ‖xᵢ‖² ≤ m`, after `k` iterations the `mse` is
within `‖θ‖² / (2ηk)` of every linear model `θ` (`mse_linRegGD_le`, the `O(1/k)` rate). -/
@[specialize] def linRegGD (cfg : GDConfig α) (data : Dataset α m n) : LinearModel α n :=
  LinearModel.ofParams (gradientDescent (mseObjective data) cfg vzero)

/-- `mseObjective` with the augmented design matrix and its transpose stored sparsely, so
each gradient costs time proportional to the number of nonzero features. Over `ℝ` it is
`mseObjective` (`mseObjectiveSparse_eq` in `Proofs/ML/Basic.lean`). On `Float` the
gradient is the same up to skipped `± 0` terms, which do not change a sum of finite numbers. -/
@[specialize] def mseObjectiveSparse (data : Dataset α m n) : Objective α (n + 1) :=
  let Xa := augmentMat data.X
  let rows := SparseMat.ofDense Xa
  let cols := SparseMat.ofDense (transpose Xa)
  { loss := fun θ => mse (LinearModel.ofParams θ) data
    grad := fun θ =>
      smul (Scalar.fromNat 2 / Scalar.fromNat m) (smatVec cols (vsub (smatVec rows θ) data.y)) }

/-- `linRegGD` on `mseObjectiveSparse`: the same iterates (`linRegGDSparse_eq`), much
faster on sparse features such as Morgan fingerprints. -/
@[specialize] def linRegGDSparse (cfg : GDConfig α) (data : Dataset α m n) : LinearModel α n :=
  LinearModel.ofParams (gradientDescent (mseObjectiveSparse data) cfg vzero)

/-- `linRegGD` that also returns the training MSE every `every` iterations. -/
@[specialize] def linRegGDWithHistory (cfg : GDConfig α) (data : Dataset α m n)
    (every : Nat := 1) : LinearModel α n × Array (Nat × α) :=
  let (θ, hist) := gradientDescentWithHistory (mseObjective data) cfg vzero every
  (LinearModel.ofParams θ, hist)

end LinearRegression

end ML

end
