/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import LeanLearn.Regression.LinearModel
public import LeanLearn.Proofs.LeastSquares.Ridge

/-!
# The executable linear model, read at `ℝ`

`Regression/LinearModel.lean` writes the prediction, squared error and ridge objective with
`sumFin`, so that they run at `Float`. At `ℝ` they are the closed-form specifications of
`Proofs/LeastSquares/`:

* `predict_real`, `residual_real`, `squaredError_real`, `penalty_real`, `ridgeLoss_real`: the
  executable definitions are `OLS.predict`, `OLS.residual`, `OLS.loss`, `Ridge.penalty` and
  `Ridge.loss`;
* `normalResidual_eq_zero_iff`: stationarity of the executable objective is exactly the ridge
  normal equations;
* `ols_fit_minimizes`, `stationary_minimizes`, `ridge_fit_minimizes`: the optimality theorems of
  the closed form, restated for the executable objectives.
-/

public section

namespace LeanLearn.Regression.LinearModel

open Matrix

variable {n p : ℕ}

/-- The executable `predictRow` at `ℝ` is the dot product `x ⬝ᵥ w`, the row-level bridge every
vector lemma below reduces to. -/
theorem predictRow_real (x w : Fin p → ℝ) : predictRow x w = x ⬝ᵥ w := sumFin_eq_sum _

/-- The executable `predict` at `ℝ` is `X *ᵥ w`, i.e. `OLS.predict`. -/
theorem predict_real (X : Design ℝ n p) (w : Fin p → ℝ) : predict X w = OLS.predict X w :=
  funext fun i ↦ predictRow_real (X i) w

/-- The executable `residual` at `ℝ` is `OLS.residual`, the vector `X *ᵥ w - y`. -/
theorem residual_real (X : Design ℝ n p) (y : Fin n → ℝ) (w : Fin p → ℝ) :
    residual X y w = OLS.residual X y w :=
  congrArg (· - y) (predict_real X w)

/-- The Float-usable OLS definition specializes to the formally verified real objective. -/
theorem squaredError_real (X : Design ℝ n p) (y : Fin n → ℝ) (w : Fin p → ℝ) :
    squaredError X y w = OLS.loss X y w := by
  simp [squaredError, sumFin_eq_sum, residual_real, OLS.loss, dotProduct]

/-- The executable `penalty` at `ℝ` is `Ridge.penalty`, with `w j * w j` read as `w j ^ 2`. -/
theorem penalty_real (weights w : Fin p → ℝ) : penalty weights w = Ridge.penalty weights w := by
  simp [penalty, sumFin_eq_sum, Ridge.penalty, pow_two]

/-- The Float-usable ridge definition specializes to the formally verified real objective. -/
theorem ridgeLoss_real (X : Design ℝ n p) (y : Fin n → ℝ) (weights w : Fin p → ℝ) :
    ridgeLoss X y weights w = Ridge.loss X y weights w := by
  rw [ridgeLoss, squaredError_real, penalty_real, Ridge.loss]

-- The executable normal residual at `ℝ` is `Xᵀ(Xw − y) + diag ρ w`, the vector whose vanishing
-- `Ridge.normalEquations_iff` identifies with the ridge normal equations.
private theorem normalResidual_real (X : Design ℝ n p) (y : Fin n → ℝ) (weights w : Fin p → ℝ) :
    normalResidual X y weights w = Xᵀ *ᵥ OLS.residual X y w + diagonal weights *ᵥ w := by
  ext j
  simp only [normalResidual, sumFin_eq_sum, residual_real, Pi.add_apply, mulVec_diagonal]
  rfl

/-- Stationarity in the shared definition is exactly the real ridge normal equations. -/
theorem normalResidual_eq_zero_iff (X : Design ℝ n p) (y : Fin n → ℝ) (weights w : Fin p → ℝ) :
    normalResidual X y weights w = 0 ↔ Ridge.NormalEquations X y weights w := by
  rw [normalResidual_real, Ridge.normalEquations_iff]

/-- Correctness of OLS expressed using the shared, executable objective definition. -/
theorem ols_fit_minimizes (X : Design ℝ n p) (y : Fin n → ℝ) (h : (OLS.gram X).det ≠ 0)
    (v : Fin p → ℝ) : squaredError X y (OLS.fit X y h) ≤ squaredError X y v := by
  simpa only [squaredError_real] using OLS.fit_minimizes X y h v

/-- Nonnegative diagonal ridge weights turn stationarity into global optimality. -/
theorem stationary_minimizes (X : Design ℝ n p) (y : Fin n → ℝ) {weights w : Fin p → ℝ}
    (hweights : ∀ j, 0 ≤ weights j) (h : normalResidual X y weights w = 0) (v : Fin p → ℝ) :
    ridgeLoss X y weights w ≤ ridgeLoss X y weights v := by
  simpa only [ridgeLoss_real] using Ridge.normalEquations_minimize X y hweights
    ((normalResidual_eq_zero_iff X y weights w).mp h) v

/-- Positive ridge's exact fit minimizes the shared ridge objective on every real design. -/
theorem ridge_fit_minimizes (X : Design ℝ n p) (y : Fin n → ℝ) (weights : Fin p → ℝ)
    (hweights : ∀ j, 0 < weights j) (v : Fin p → ℝ) :
    ridgeLoss X y weights (Ridge.fitPositive X y weights hweights) ≤ ridgeLoss X y weights v := by
  simpa only [ridgeLoss_real] using Ridge.fitPositive_minimizes X y weights hweights v

end LeanLearn.Regression.LinearModel
