/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanLearn.Proofs.Regression.Basic
public import LeanLearn.Proofs.LeastSquares.Ridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# LeanLearn.Proofs.Regression.MatrixBridge

The two regression formulations are one problem.

`Regression/Problem.lean` writes ridge regression on `m` samples as the *averaged* loss
`L(θ) = (1/m) ∑ᵣ (⟪xᵣ, θ⟫ − yᵣ)² + λ ‖θ‖²` over executable `Vec`s, with normal equations
`A θ = b`. `Proofs/LeastSquares/OLS.lean` and `Ridge.lean` write it as the *unaveraged* matrix loss
`‖Xw − y‖² + Σⱼ ρⱼ wⱼ²` over Mathlib's `Matrix`. Over `ℝ`, with `X` the design matrix of the
problem (every sample with its constant `1` appended), `y` its targets and `ρ = m λ` on every
coefficient,

  `‖Xθ − y‖² + m λ ‖θ‖² = m · L(θ)`,   `XᵀX + m λ I = m · A`,   `Xᵀ y = m · b`.

The averaging is the whole difference: it does not move the minimizers, but it rescales the
penalty, so the `Problem` with `λ` is the `Ridge` problem with `ρ = m λ`. For `m > 0` the two
have the same normal equations and the same minimizers, and the matrix layer's theorems
transfer:

* **The dictionary** (`designMatrix`, `target`, `ofVec`): `predict_designMatrix`,
  `ridge_loss_eq` / `loss_eq_ridge_loss`, `gram_apply`, `transpose_mulVec_target`.
* **Normal equations** (`residual_eq_zero_iff_normalEquations`): `A θ = b` is exactly
  `(XᵀX + m λ I) θ = Xᵀ y`.
* **Minimizers** (`isMinimizer_iff`): `θ` minimises `L` iff it minimises the matrix loss.
* **Existence, uniqueness and the closed form** (`closedForm`, `closedForm_isMinimizer`,
  `isMinimizer_unique`, `existsUnique_isMinimizer`): for `λ > 0` the problem has exactly one
  minimizer, `(XᵀX + m λ I)⁻¹ Xᵀ y`, whatever the design — from
  `Ridge.exists_unique_minimizer`.
* **The trade-off** (`dot_self_le_of_isMinimizer`, `dot_self_antitone`, `mse_monotone`):
  raising `λ` can only shrink the minimizer's `‖θ‖²` and raise its mean squared error. This is
  the ridge-against-OLS trade-off of the matrix layer; it needs no bridge — comparing two
  minimizers against each other proves it for `L` directly, for every `m`.

At `m = 0` the loss identity still holds (both sides are `0`), but `L(θ) = λ ‖θ‖²` while the
matrix problem is empty, so the statements about normal equations and minimizers assume
`m > 0`.
-/

@[expose] public section

namespace LeanLearn.Regression

open Finset Matrix
open scoped Matrix

/-! ## `Vec` as a Mathlib vector -/

section Vec

variable {n : ℕ}

/-- A `Vec` read as a Mathlib vector `Fin n → ℝ`; `Vector.ofFn` reads it back. -/
def ofVec (θ : Vec ℝ n) : Fin n → ℝ := fun i ↦ θ[i]

/-- Entry `i` of `ofVec θ` is `θ[i]`. -/
@[simp] theorem ofVec_apply (θ : Vec ℝ n) (i : Fin n) : ofVec θ i = θ[i] := rfl

/-- `ofVec` undoes `Vector.ofFn`. -/
@[simp] theorem ofVec_ofFn (f : Fin n → ℝ) : ofVec (Vector.ofFn f) = f :=
  funext fun i ↦ Vector.getElem_ofFn i.isLt

/-- `Vector.ofFn` undoes `ofVec`: the two are inverse bijections between `Vec ℝ n` and
`Fin n → ℝ`. -/
@[simp] theorem ofFn_ofVec (θ : Vec ℝ n) : Vector.ofFn (ofVec θ) = θ := Vector.ofFn_getElem

/-- The executable inner product is Mathlib's. -/
theorem dot_eq_dotProduct (u v : Vec ℝ n) : dot u v = ofVec u ⬝ᵥ ofVec v := dot_eq_sum u v

/-- A constant diagonal penalty `c` on a `Vec` is `c ‖θ‖²`. -/
theorem penalty_const (c : ℝ) (θ : Vec ℝ n) :
    Ridge.penalty (fun _ ↦ c) (ofVec θ) = c * dot θ θ := by
  simp [Ridge.penalty, dot_eq_sum, mul_sum, sq]

end Vec

namespace Problem

variable {m d : ℕ} (P : Problem ℝ m d)

/-! ## The dictionary -/

/-- The design matrix of `P` as a Mathlib matrix: row `r` is sample `r` with the constant `1`
appended. -/
noncomputable def designMatrix : Matrix (Fin m) (Fin (d + 1)) ℝ := of fun r i ↦ P.feature r i

/-- The targets of `P` as a Mathlib vector. -/
noncomputable def target : Fin m → ℝ := fun r ↦ P.y[r]

/-- Entry `(r, i)` of the design matrix is feature `i` of sample `r` (the constant `1` at
`i = d`). -/
@[simp] theorem designMatrix_apply (r : Fin m) (i : Fin (d + 1)) :
    P.designMatrix r i = P.feature r i := rfl

/-- Entry `r` of `target` is the target `yᵣ`. -/
@[simp] theorem target_apply (r : Fin m) : P.target r = P.y[r] := rfl

/-- `Xθ` is the vector of fitted values `⟪xᵣ, θ⟫`. -/
theorem predict_designMatrix (θ : Vec ℝ (d + 1)) (r : Fin m) :
    OLS.predict P.designMatrix (ofVec θ) r = P.fitted r θ := by
  simp [OLS.predict, mulVec, dotProduct, fitted_eq]

/-- `Xθ − y` is the vector of residuals `⟪xᵣ, θ⟫ − yᵣ`. -/
theorem residual_designMatrix (θ : Vec ℝ (d + 1)) (r : Fin m) :
    OLS.residual P.designMatrix P.target (ofVec θ) r = P.fitted r θ - P.y[r] := by
  simp [OLS.residual, predict_designMatrix]

/-- The mean squared error `(1/m) ∑ᵣ (⟪xᵣ, θ⟫ − yᵣ)²`: the loss without its penalty. -/
noncomputable def mse (θ : Vec ℝ (d + 1)) : ℝ := (∑ r, (P.fitted r θ - P.y[r]) ^ 2) / m

/-- The loss is the mean squared error plus the penalty: `L(θ) = MSE(θ) + λ ‖θ‖²`. -/
theorem loss_eq_mse_add (θ : Vec ℝ (d + 1)) : P.loss θ = P.mse θ + P.ridge * dot θ θ := by
  simp only [loss_eq, mse, dot_eq_sum, sq]

/-- `‖Xθ − y‖² = m · MSE(θ)`, for every `m`. -/
theorem ols_loss_eq (θ : Vec ℝ (d + 1)) :
    OLS.loss P.designMatrix P.target (ofVec θ) = m * P.mse θ := by
  simp only [OLS.loss_eq_sum, mse, predict_designMatrix, target_apply]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hm.ne')]

/-- `MSE(θ) = (1/m) ‖Xθ − y‖²`, for `m > 0`. -/
theorem mse_eq_ols_loss (hm : 0 < m) (θ : Vec ℝ (d + 1)) :
    P.mse θ = (1 / m) * OLS.loss P.designMatrix P.target (ofVec θ) := by
  rw [ols_loss_eq, one_div, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hm.ne')]

/-- **The losses agree up to the factor `m`**, for every `m`:
`‖Xθ − y‖² + m λ ‖θ‖² = m · L(θ)`. (At `m = 0` both sides are `0`.) -/
theorem ridge_loss_eq (θ : Vec ℝ (d + 1)) :
    Ridge.loss P.designMatrix P.target (fun _ ↦ m * P.ridge) (ofVec θ) = m * P.loss θ := by
  rw [Ridge.loss, ols_loss_eq, penalty_const, loss_eq_mse_add]
  ring

/-- **The loss is the averaged matrix ridge loss**, for `m > 0`:
`L(θ) = (1/m) (‖Xθ − y‖² + m λ ‖θ‖²)`. -/
theorem loss_eq_ridge_loss (hm : 0 < m) (θ : Vec ℝ (d + 1)) :
    P.loss θ = (1 / m) * Ridge.loss P.designMatrix P.target (fun _ ↦ m * P.ridge) (ofVec θ) := by
  rw [ridge_loss_eq, one_div, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hm.ne')]

/-- **The normal matrix is the averaged regularized Gram matrix**: `XᵀX + m λ I = m · A`,
for `m > 0`. -/
theorem gram_apply (hm : 0 < m) (i j : Fin (d + 1)) :
    Ridge.gram P.designMatrix (fun _ ↦ m * P.ridge) i j = m * P.normalMatrix[i][j] := by
  rw [normalMatrix_apply, mul_add, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hm.ne')]
  simp [Ridge.gram, OLS.gram, mul_apply, diagonal_apply]

/-- **The normal vector is the averaged `Xᵀy`**: `Xᵀ y = m · b`, for `m > 0`. -/
theorem transpose_mulVec_target (hm : 0 < m) (i : Fin (d + 1)) :
    (P.designMatrixᵀ *ᵥ P.target) i = m * P.normalVector[i] := by
  rw [normalVector_apply, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hm.ne')]
  simp [mulVec, dotProduct]

/-! ## The normal equations -/

/-- **The normal equations agree**, for `m > 0`: `A θ = b` is exactly
`(XᵀX + m λ I) θ = Xᵀ y`. -/
theorem residual_eq_zero_iff_normalEquations (hm : 0 < m) (θ : Vec ℝ (d + 1)) :
    (∀ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] = 0) ↔
      Ridge.NormalEquations P.designMatrix P.target (fun _ ↦ m * P.ridge) (ofVec θ) := by
  -- entrywise, `(XᵀX + m λ I) θ = m (A θ - b) + Xᵀ y`
  have key (i : Fin (d + 1)) : (Ridge.gram P.designMatrix (fun _ ↦ m * P.ridge) *ᵥ ofVec θ) i =
      m * (residual P.normalMatrix P.normalVector θ)[i] + (P.designMatrixᵀ *ᵥ P.target) i := by
    rw [residual, vsub_getElem, matVec_getElem, transpose_mulVec_target P hm, mul_sub,
      sub_add_cancel]
    simp only [mulVec, dotProduct, ofVec_apply, gram_apply P hm, mul_assoc, ← mul_sum]
  simp [Ridge.NormalEquations, funext_iff, key, hm.ne']

/-! ## Minimizers -/

/-- `θ` minimises the loss of `P` over all parameters. -/
def IsMinimizer (θ : Vec ℝ (d + 1)) : Prop := ∀ u, P.loss θ ≤ P.loss u

/-- **The minimizers agree**, for `m > 0`: `θ` minimises `L` iff it minimises the matrix
ridge loss with weights `m λ`. -/
theorem isMinimizer_iff (hm : 0 < m) (θ : Vec ℝ (d + 1)) :
    P.IsMinimizer θ ↔
      Ridge.IsMinimizer P.designMatrix P.target (fun _ ↦ m * P.ridge) (ofVec θ) := by
  -- every matrix parameter is some `ofVec u`, and the losses agree up to the factor `m`
  have hsurj : Function.Surjective (ofVec (n := d + 1)) := fun v ↦ ⟨Vector.ofFn v, ofVec_ofFn v⟩
  rw [Ridge.IsMinimizer, hsurj.forall]
  simp only [IsMinimizer, ridge_loss_eq, mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hm)]

/-- The closed-form solution `(XᵀX + m λ I)⁻¹ Xᵀ y` as a `Vec`, for `m > 0` and `λ > 0`. -/
noncomputable def closedForm (hm : 0 < m) (hridge : 0 < P.ridge) : Vec ℝ (d + 1) :=
  Vector.ofFn (Ridge.fitPositive P.designMatrix P.target (fun _ ↦ m * P.ridge)
    fun _ ↦ mul_pos (Nat.cast_pos.mpr hm) hridge)

/-- The closed form minimises the loss. -/
theorem closedForm_isMinimizer (hm : 0 < m) (hridge : 0 < P.ridge) :
    P.IsMinimizer (P.closedForm hm hridge) := by
  rw [isMinimizer_iff P hm, closedForm, ofVec_ofFn]
  exact Ridge.fitPositive_minimizes _ _ _ _

/-- Every minimizer is the closed form. -/
theorem isMinimizer_unique (hm : 0 < m) (hridge : 0 < P.ridge) {θ : Vec ℝ (d + 1)}
    (h : P.IsMinimizer θ) : θ = P.closedForm hm hridge := by
  rw [closedForm, ← Ridge.fitPositive_unique _ _ _ _ ((P.isMinimizer_iff hm θ).mp h), ofFn_ofVec]

/-- **Existence and uniqueness**: for `m > 0` and `λ > 0` the problem has exactly one
minimizer, whatever the design — even with fewer samples than features. -/
theorem existsUnique_isMinimizer (hm : 0 < m) (hridge : 0 < P.ridge) :
    ∃! θ : Vec ℝ (d + 1), P.IsMinimizer θ :=
  ⟨P.closedForm hm hridge, P.closedForm_isMinimizer hm hridge,
    fun _ ↦ P.isMinimizer_unique hm hridge⟩

/-! ## The trade-off -/

/-- The same data with ridge penalty `l`; `P.withRidge 0` is least squares. -/
def withRidge (l : ℝ) : Problem ℝ m d := { P with ridge := l }

/-- `withRidge` keeps the features. -/
@[simp] theorem withRidge_X (l : ℝ) : (P.withRidge l).X = P.X := rfl

/-- `withRidge` keeps the targets. -/
@[simp] theorem withRidge_y (l : ℝ) : (P.withRidge l).y = P.y := rfl

/-- `withRidge l` has penalty `l`. -/
@[simp] theorem withRidge_ridge (l : ℝ) : (P.withRidge l).ridge = l := rfl

/-- `withRidge` keeps the design matrix. -/
@[simp] theorem withRidge_designMatrix (l : ℝ) :
    (P.withRidge l).designMatrix = P.designMatrix := rfl

/-- `withRidge` keeps the target vector. -/
@[simp] theorem withRidge_target (l : ℝ) : (P.withRidge l).target = P.target := rfl

/-- `withRidge` keeps the mean squared error: the penalty does not enter it. -/
@[simp] theorem withRidge_mse (l : ℝ) (θ : Vec ℝ (d + 1)) : (P.withRidge l).mse θ = P.mse θ := rfl

/-- Reinstalling the problem's own penalty changes nothing. -/
theorem withRidge_self : P.withRidge P.ridge = P := rfl

/-- Least squares on the data of `P` minimises the mean squared error. -/
theorem loss_withRidge_zero (θ : Vec ℝ (d + 1)) : (P.withRidge 0).loss θ = P.mse θ := by
  simp [loss_eq_mse_add]

/-- **A stronger penalty shrinks the minimizer**: for `a < b`, a minimizer at penalty `b` has
no larger `‖θ‖²` than one at penalty `a`. -/
theorem dot_self_antitone {a b : ℝ} (hab : a < b) {θ₁ θ₂ : Vec ℝ (d + 1)}
    (h₁ : (P.withRidge a).IsMinimizer θ₁) (h₂ : (P.withRidge b).IsMinimizer θ₂) :
    dot θ₂ θ₂ ≤ dot θ₁ θ₁ := by
  -- each minimizer beats the other on its own loss, and the two losses differ only in the
  -- penalty, so `(b - a) ‖θ₂‖² ≤ (b - a) ‖θ₁‖²`
  have e₁ := h₁ θ₂
  have e₂ := h₂ θ₁
  simp only [loss_eq_mse_add, withRidge_mse, withRidge_ridge] at e₁ e₂
  exact le_of_mul_le_mul_left (by linarith) (sub_pos.mpr hab)

/-- **Ridge shrinks**: for `λ > 0`, a minimizer of `P` has no larger `‖θ‖²` than any
least-squares minimizer on the same data — and, by definition of the latter, no smaller mean
squared error. The case `a = 0`, `b = λ` of `dot_self_antitone`. -/
theorem dot_self_le_of_isMinimizer (hridge : 0 < P.ridge) {θ₀ θ : Vec ℝ (d + 1)}
    (h₀ : (P.withRidge 0).IsMinimizer θ₀) (h : P.IsMinimizer θ) : dot θ θ ≤ dot θ₀ θ₀ :=
  P.dot_self_antitone hridge h₀ h

/-- **... and raises its error**: for `0 ≤ a < b`, a minimizer at penalty `b` has no smaller
mean squared error than one at penalty `a`. -/
theorem mse_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {θ₁ θ₂ : Vec ℝ (d + 1)}
    (h₁ : (P.withRidge a).IsMinimizer θ₁) (h₂ : (P.withRidge b).IsMinimizer θ₂) :
    P.mse θ₁ ≤ P.mse θ₂ := by
  have e₁ := h₁ θ₂
  simp only [loss_eq_mse_add, withRidge_mse, withRidge_ridge] at e₁
  linarith [mul_le_mul_of_nonneg_left (P.dot_self_antitone hab h₁ h₂) ha]

end Problem

end LeanLearn.Regression
