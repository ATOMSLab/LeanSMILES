/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ordinary least squares over the real numbers

Rows of `X` are observations and columns are features; `y` contains the targets.
An intercept is an ordinary coefficient whose column in `X` consists of ones.
No SMILES conversion, data loading, or training/test split is required here.

The objective is the unregularized sum of squared errors `‖Xw - y‖²`.
`normalEquations_minimize` proves that any solution of the normal equations
is a global minimizer, even for a singular design. `fit` defines the exact
closed-form solution `(XᵀX)⁻¹ Xᵀy` with an explicit nonsingularity hypothesis.
`fit_minimizes` and `fit_unique` certify its optimality and uniqueness.

These are exact statements over `ℝ`. They do not assert numerical stability
of matrix inversion or correctness of a floating-point implementation.
-/

@[expose] public section

namespace LeanLearn.Regression.OLS

open Matrix
open scoped Matrix

noncomputable section

variable {n p : ℕ}

/-- Predicted targets, one per observation: `Xw`. -/
def predict (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin p → ℝ) : Fin n → ℝ :=
  X *ᵥ w

/-- Prediction minus observed target: `Xw - y`. -/
def residual (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (w : Fin p → ℝ) : Fin n → ℝ :=
  predict X w - y

/-- Unregularized sum of squared errors, expressed as a dot product. -/
def loss (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (w : Fin p → ℝ) : ℝ :=
  residual X y w ⬝ᵥ residual X y w

/-- `w` is a global minimizer among all coefficient vectors. -/
def IsMinimizer (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (w : Fin p → ℝ) : Prop :=
  ∀ v, loss X y w ≤ loss X y v

/-- The normal equations say that the residual is orthogonal to every feature column. -/
def NormalEquations (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (w : Fin p → ℝ) : Prop :=
  Xᵀ *ᵥ residual X y w = 0

/-- The Gram matrix of the design: `XᵀX`. -/
def gram (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Xᵀ * X

/-- The dot-product definition is exactly the familiar sum of squared errors. -/
theorem loss_eq_sum (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (w : Fin p → ℝ) :
    loss X y w = ∑ i, (predict X w i - y i) ^ 2 := by
  simp [loss, residual, dotProduct, pow_two]

/-- Squared-error loss is always nonnegative. -/
theorem loss_nonneg (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (w : Fin p → ℝ) :
    0 ≤ loss X y w := by
  rw [loss_eq_sum]
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _

/-- The residual form of the normal equations is equivalent to `XᵀXw = Xᵀy`. -/
theorem normalEquations_iff (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (w : Fin p → ℝ) :
    NormalEquations X y w ↔ gram X *ᵥ w = Xᵀ *ᵥ y := by
  simp [NormalEquations, residual, predict, gram, mulVec_sub, mulVec_mulVec, sub_eq_zero]

/-- Changing the coefficients by `d` changes predictions and residuals by `Xd`. -/
theorem residual_add (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (w d : Fin p → ℝ) :
    residual X y (w + d) = residual X y w + predict X d := by
  simp only [residual, predict, mulVec_add, add_sub_right_comm]

/-- Under the normal equations, the residual is orthogonal to every prediction change. -/
theorem residual_dot_predict_eq_zero (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    {w : Fin p → ℝ} (h : NormalEquations X y w) (d : Fin p → ℝ) :
    residual X y w ⬝ᵥ predict X d = 0 := by
  rw [predict, dotProduct_mulVec, ← mulVec_transpose, h, zero_dotProduct]

/-- The key identity: at a normal-equation solution, changing `w` adds `‖Xd‖²` to loss. -/
theorem loss_add_of_normalEquations (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    {w : Fin p → ℝ} (h : NormalEquations X y w) (d : Fin p → ℝ) :
    loss X y (w + d) = loss X y w + predict X d ⬝ᵥ predict X d := by
  simp [loss, residual_add, residual_dot_predict_eq_zero X y h,
    dotProduct_comm (predict X d) (residual X y w)]

/-- Every normal-equation solution globally minimizes squared error; no rank assumption. -/
theorem normalEquations_minimize (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) {w : Fin p → ℝ}
    (h : NormalEquations X y w) : IsMinimizer X y w := by
  intro v
  rw [← add_sub_cancel w v, loss_add_of_normalEquations X y h]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)

/-- Exact OLS coefficients. The hypothesis excludes singular Gram matrices. -/
def fit (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (_h : (gram X).det ≠ 0) : Fin p → ℝ :=
  (gram X)⁻¹ *ᵥ (Xᵀ *ᵥ y)

/-- The closed-form coefficients satisfy the normal equations. -/
theorem fit_normalEquations (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (h : (gram X).det ≠ 0) :
    NormalEquations X y (fit X y h) := by
  rw [normalEquations_iff, fit, mulVec_mulVec, mul_nonsing_inv _ h.isUnit, one_mulVec]

/-- Correctness of the closed-form algorithm: its output is a global minimizer. -/
theorem fit_minimizes (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (h : (gram X).det ≠ 0) :
    IsMinimizer X y (fit X y h) :=
  normalEquations_minimize X y (fit_normalEquations X y h)

/-- With nonsingular `XᵀX`, distinct coefficients cannot have identical predictions. -/
theorem predict_injective (X : Matrix (Fin n) (Fin p) ℝ) (h : (gram X).det ≠ 0) :
    Function.Injective (predict X) := fun u v huv ↦
  mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr h.isUnit) <| by
    simpa [predict, mulVec_mulVec, gram] using congrArg (Xᵀ *ᵥ ·) huv

/-- Any global minimizer equals `fit` when the Gram matrix is nonsingular. -/
theorem fit_unique (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (h : (gram X).det ≠ 0)
    {w : Fin p → ℝ} (hw : IsMinimizer X y w) : w = fit X y h := by
  have heq := loss_add_of_normalEquations X y (fit_normalEquations X y h) (w - fit X y h)
  rw [add_sub_cancel] at heq
  have hzero : predict X (w - fit X y h) ⬝ᵥ predict X (w - fit X y h) = 0 :=
    le_antisymm (by linarith [hw (fit X y h)]) (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _)
  exact sub_eq_zero.mp <| predict_injective X h <| by
    simpa [predict] using dotProduct_self_eq_zero.mp hzero

end

end LeanLearn.Regression.OLS
