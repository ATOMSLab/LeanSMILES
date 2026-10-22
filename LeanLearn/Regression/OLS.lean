/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct
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

namespace LeanLearn.Regression.OLS

open Matrix
open scoped BigOperators Matrix

noncomputable section

variable {n p : ℕ}

/-- Predicted targets, one per observation: `Xw`. -/
def predict (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin p → ℝ) : Fin n → ℝ :=
  X *ᵥ w

/-- Prediction minus observed target: `Xw - y`. -/
def residual (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (w : Fin p → ℝ) : Fin n → ℝ :=
  predict X w - y

/-- Unregularized sum of squared errors, expressed as a dot product. -/
def loss (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (w : Fin p → ℝ) : ℝ :=
  residual X y w ⬝ᵥ residual X y w

/-- `w` is a global minimizer among all coefficient vectors. -/
def IsMinimizer (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (w : Fin p → ℝ) : Prop :=
  ∀ v, loss X y w ≤ loss X y v

/-- The normal equations say that the residual is orthogonal to every feature column. -/
def NormalEquations (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (w : Fin p → ℝ) : Prop :=
  Xᵀ *ᵥ residual X y w = 0

/-- The Gram matrix of the design: `XᵀX`. -/
def gram (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Xᵀ * X

/-- The dot-product definition is exactly the familiar sum of squared errors. -/
theorem loss_eq_sum (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (w : Fin p → ℝ) : loss X y w = ∑ i, (predict X w i - y i) ^ 2 := by
  simp [loss, residual, dotProduct, pow_two]

/-- Squared-error loss is always nonnegative. -/
theorem loss_nonneg (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (w : Fin p → ℝ) : 0 ≤ loss X y w := by
  rw [loss_eq_sum]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The residual form of the normal equations is equivalent to `XᵀXw = Xᵀy`. -/
theorem normalEquations_iff (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (w : Fin p → ℝ) : NormalEquations X y w ↔ gram X *ᵥ w = Xᵀ *ᵥ y := by
  simp [NormalEquations, residual, predict, gram, mulVec_sub, mulVec_mulVec, sub_eq_zero]

/-- Changing the coefficients by `d` changes predictions and residuals by `Xd`. -/
theorem residual_add (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (w d : Fin p → ℝ) : residual X y (w + d) = residual X y w + predict X d := by
  ext i
  simp only [residual, predict, mulVec_add, Pi.sub_apply, Pi.add_apply]
  ring

/-- Under the normal equations, the residual is orthogonal to every prediction change. -/
theorem residual_dot_predict_eq_zero (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) {w : Fin p → ℝ} (h : NormalEquations X y w)
    (d : Fin p → ℝ) : residual X y w ⬝ᵥ predict X d = 0 := by
  change Xᵀ *ᵥ residual X y w = 0 at h
  rw [predict, dotProduct_mulVec, ← mulVec_transpose, h, zero_dotProduct]

/-- The key identity: at a normal-equation solution, changing `w` adds `‖Xd‖²` to loss. -/
theorem loss_add_of_normalEquations (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) {w : Fin p → ℝ} (h : NormalEquations X y w)
    (d : Fin p → ℝ) :
    loss X y (w + d) = loss X y w + predict X d ⬝ᵥ predict X d := by
  have hcross := residual_dot_predict_eq_zero X y h d
  simp only [loss, residual_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm (predict X d) (residual X y w), hcross]
  ring

/-- Every normal-equation solution globally minimizes squared error; no rank assumption. -/
theorem normalEquations_minimize (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) {w : Fin p → ℝ} (h : NormalEquations X y w) :
    IsMinimizer X y w := by
  intro v
  have hadd : w + (v - w) = v := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have heq := loss_add_of_normalEquations X y h (v - w)
  rw [hadd] at heq
  have hnonneg : 0 ≤ predict X (v - w) ⬝ᵥ predict X (v - w) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  linarith

/-- Exact OLS coefficients. The hypothesis excludes singular Gram matrices. -/
def fit (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (_h : (gram X).det ≠ 0) : Fin p → ℝ :=
  (gram X)⁻¹ *ᵥ (Xᵀ *ᵥ y)

/-- The closed-form coefficients satisfy the normal equations. -/
theorem fit_normalEquations (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (h : (gram X).det ≠ 0) : NormalEquations X y (fit X y h) := by
  rw [normalEquations_iff]
  rw [fit, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h), one_mulVec]

/-- Correctness of the closed-form algorithm: its output is a global minimizer. -/
theorem fit_minimizes (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (h : (gram X).det ≠ 0) : IsMinimizer X y (fit X y h) :=
  normalEquations_minimize X y (fit_normalEquations X y h)

/-- With nonsingular `XᵀX`, distinct coefficients cannot have identical predictions. -/
theorem predict_injective (X : Matrix (Fin n) (Fin p) ℝ)
    (h : (gram X).det ≠ 0) : Function.Injective (predict X) := by
  intro u v huv
  have heq := congrArg (fun z => (gram X)⁻¹ *ᵥ (Xᵀ *ᵥ z)) huv
  simp only [predict, mulVec_mulVec] at heq
  change ((gram X)⁻¹ * gram X) *ᵥ u = ((gram X)⁻¹ * gram X) *ᵥ v at heq
  simpa only [nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), one_mulVec] using heq

/-- Any global minimizer equals `fit` when the Gram matrix is nonsingular. -/
theorem fit_unique (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (h : (gram X).det ≠ 0) {w : Fin p → ℝ} (hw : IsMinimizer X y w) :
    w = fit X y h := by
  let f := fit X y h
  have hadd : f + (w - f) = w := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have heq := loss_add_of_normalEquations X y (fit_normalEquations X y h) (w - f)
  change loss X y (f + (w - f)) = loss X y f +
    predict X (w - f) ⬝ᵥ predict X (w - f) at heq
  rw [hadd] at heq
  have hnonneg : 0 ≤ predict X (w - f) ⬝ᵥ predict X (w - f) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hle := hw f
  have hzero : predict X (w - f) ⬝ᵥ predict X (w - f) = 0 := by linarith
  have hpred := dotProduct_self_eq_zero.mp hzero
  have hcoeff : w - f = 0 := predict_injective X h (by simpa [predict] using hpred)
  exact sub_eq_zero.mp hcoeff

end

end LeanLearn.Regression.OLS
