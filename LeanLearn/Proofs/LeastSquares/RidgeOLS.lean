/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanLearn.Proofs.LeastSquares.Ridge
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ridge regression against ordinary least squares

`OLS.lean` and `Ridge.lean` each prove that their closed form minimizes its own loss. This file
is about the two models together: what the penalty buys, what it costs, and how the ridge
solution moves as the penalty moves.

Throughout, `X : Matrix (Fin n) (Fin p) ℝ`, `y : Fin n → ℝ`, `ρ : Fin p → ℝ` is the diagonal
penalty, and `l` is a scalar penalty (`ρ = fun _ ↦ l`).

* **Zero penalty is OLS** (`isMinimizer_zero_penalty`, completing `loss_zero_penalty`,
  `normalEquations_zero_penalty`, `fit_zero_penalty`), and **ridge is OLS on more data**
  (`isMinimizer_iff_augmented`: the minimizers coincide with those of OLS on the
  square-root-penalty augmented design).
* **The trade-off** (`penalty_le_of_isMinimizer`): against any OLS minimizer `w₀`, a ridge
  minimizer `w` has `Σⱼ ρⱼ wⱼ² ≤ Σⱼ ρⱼ (w₀)ⱼ²` — it pays in squared error
  (`OLS.loss w₀ ≤ OLS.loss w`, which is just what `w₀` being an OLS minimizer says) to buy a
  smaller penalized norm. No rank or sign assumption. More generally the penalized norm is
  antitone and the squared error monotone in the penalty strength (`penalty_antitone`,
  `ols_loss_monotone`).
* **Ridge is a linear shrinkage of OLS** (`fit_eq_shrink_ols_fit`):
  `wρ = (XᵀX + diag ρ)⁻¹ XᵀX w₀`. For orthonormal columns, `XᵀX = 1`, this is the textbook
  `wλ = w₀ / (1 + λ)` (`fit_eq_smul_ols_fit_of_gram_eq_one`).
* **The ridge path** `path X y l = (XᵀX + l I)⁻¹ Xᵀy` is continuous wherever the regularized
  Gram matrix is nonsingular, hence on all of `l > 0` for every design (`continuousOn_path`);
  as `l → 0` it converges to OLS when `XᵀX` is nonsingular (`tendsto_path_nhds_zero`); and
  `‖wₗ‖² ≤ ‖y‖² / l` (`sum_sq_le_of_isMinimizer`), so `‖wₗ‖² → 0` as `l → ∞`
  (`tendsto_sum_sq_path_atTop`).

Exact statements over `ℝ`, as in `OLS.lean` and `Ridge.lean`.
-/

@[expose] public section

namespace LeanLearn.Regression.Ridge

open Matrix Filter Topology
open scoped Matrix
noncomputable section
variable {n p : ℕ}

/-! ## Zero penalty is OLS; ridge is OLS on more data -/

/-- At zero penalty the ridge minimizers are the OLS minimizers. -/
@[simp] theorem isMinimizer_zero_penalty (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (w : Fin p → ℝ) : IsMinimizer X y 0 w ↔ OLS.IsMinimizer X y w := by
  simp [IsMinimizer, OLS.IsMinimizer]

/-- Ridge with nonnegative weights has exactly the minimizers of OLS on the augmented design
`[X; diag √ρ]` with targets `[y; 0]`: the penalty is `p` extra observations. -/
theorem isMinimizer_iff_augmented (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) {ρ : Fin p → ℝ}
    (hρ : ∀ j, 0 ≤ ρ j) (w : Fin p → ℝ) :
    IsMinimizer X y ρ w ↔ OLS.IsMinimizer (augmentedDesign X ρ) (augmentedTargets y) w := by
  simp only [IsMinimizer, OLS.IsMinimizer, augmented_loss X y hρ]

/-! ## The trade-off -/

/-- The penalty only adds to the squared error. -/
theorem ols_loss_le_loss (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) {ρ : Fin p → ℝ}
    (hρ : ∀ j, 0 ≤ ρ j) (w : Fin p → ℝ) : OLS.loss X y w ≤ loss X y ρ w :=
  le_add_of_nonneg_right (penalty_nonneg hρ w)

/-- **Ridge shrinks.** A ridge minimizer has no larger penalized norm than any OLS minimizer.
Together with `h₀ w : OLS.loss X y w₀ ≤ OLS.loss X y w`, this is the trade-off: ridge gives up
squared error for a smaller `Σⱼ ρⱼ wⱼ²`. No assumption on `X` or on the sign of `ρ`. -/
theorem penalty_le_of_isMinimizer (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    {ρ w₀ w : Fin p → ℝ} (h₀ : OLS.IsMinimizer X y w₀) (h : IsMinimizer X y ρ w) :
    penalty ρ w ≤ penalty ρ w₀ :=
  le_of_add_le_add_left ((h w₀).trans (add_le_add_left (h₀ w) _))

/-- The closed forms: positive ridge's coefficients have a smaller penalized norm than OLS's. -/
theorem penalty_fitPositive_le (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) {ρ : Fin p → ℝ}
    (hρ : ∀ j, 0 < ρ j) (h : (OLS.gram X).det ≠ 0) :
    penalty ρ (fitPositive X y ρ hρ) ≤ penalty ρ (OLS.fit X y h) :=
  penalty_le_of_isMinimizer X y (OLS.fit_minimizes X y h) (fitPositive_minimizes X y ρ hρ)

/-- The penalty is linear in its weights: scaling `ρ` by `a` scales `penalty ρ w` by `a`. This is
what turns a comparison of penalty strengths into a scalar inequality. -/
theorem penalty_smul (a : ℝ) (ρ w : Fin p → ℝ) : penalty (a • ρ) w = a * penalty ρ w := by
  simp [penalty, Finset.mul_sum, mul_assoc]

/-- Strengthening the penalty (same shape `ρ`, larger multiple) shrinks the minimizer's
penalized norm. -/
theorem penalty_antitone (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) {a b : ℝ} (hab : a < b)
    {ρ w₁ w₂ : Fin p → ℝ} (h₁ : IsMinimizer X y (a • ρ) w₁) (h₂ : IsMinimizer X y (b • ρ) w₂) :
    penalty ρ w₂ ≤ penalty ρ w₁ := by
  have e₁ := h₁ w₂
  have e₂ := h₂ w₁
  simp only [loss, penalty_smul] at e₁ e₂
  exact le_of_mul_le_mul_left (by linarith) (sub_pos.mpr hab)

/-- ... and raises the squared error. -/
theorem ols_loss_monotone (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) {ρ w₁ w₂ : Fin p → ℝ} (h₁ : IsMinimizer X y (a • ρ) w₁)
    (h₂ : IsMinimizer X y (b • ρ) w₂) : OLS.loss X y w₁ ≤ OLS.loss X y w₂ := by
  have e₁ := h₁ w₂
  simp only [loss, penalty_smul] at e₁
  linarith [mul_le_mul_of_nonneg_left (penalty_antitone X y hab h₁ h₂) ha]

/-! ## Ridge is a linear shrinkage of OLS -/

/-- At a nonsingular regularized Gram matrix, the ridge fit is a linear image of any solution
`w₀` of the OLS normal equations: `wρ = (XᵀX + diag ρ)⁻¹ (XᵀX) w₀`. -/
theorem fit_eq_of_ols_normalEquations (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (ρ : Fin p → ℝ)
    (h : (gram X ρ).det ≠ 0) {w₀ : Fin p → ℝ} (h₀ : OLS.NormalEquations X y w₀) :
    fit X y ρ h = (gram X ρ)⁻¹ *ᵥ (OLS.gram X *ᵥ w₀) := by
  rw [fit, (OLS.normalEquations_iff X y w₀).mp h₀]

/-- Ridge applies the shrinkage matrix `(XᵀX + diag ρ)⁻¹ XᵀX` to the OLS coefficients. -/
theorem fit_eq_shrink_ols_fit (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (ρ : Fin p → ℝ)
    (h : (gram X ρ).det ≠ 0) (h₀ : (OLS.gram X).det ≠ 0) :
    fit X y ρ h = ((gram X ρ)⁻¹ * OLS.gram X) *ᵥ OLS.fit X y h₀ := by
  rw [fit_eq_of_ols_normalEquations X y ρ h (OLS.fit_normalEquations X y h₀), mulVec_mulVec]

/-- A scalar penalty: the regularized Gram matrix is `XᵀX + l I`. -/
theorem gram_const (X : Matrix (Fin n) (Fin p) ℝ) (l : ℝ) :
    gram X (fun _ ↦ l) = OLS.gram X + l • (1 : Matrix (Fin p) (Fin p) ℝ) := by
  rw [gram, smul_one_eq_diagonal]

/-- **Orthonormal columns.** When `XᵀX = 1`, ridge scales every OLS coefficient by
`1 / (1 + l)`. -/
theorem fit_eq_smul_ols_fit_of_gram_eq_one (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (hX : OLS.gram X = 1) {l : ℝ} (hl : 1 + l ≠ 0) (h : (gram X (fun _ ↦ l)).det ≠ 0)
    (h₀ : (OLS.gram X).det ≠ 0) : fit X y (fun _ ↦ l) h = (1 + l)⁻¹ • OLS.fit X y h₀ := by
  have hG : gram X (fun _ ↦ l) = (1 + l) • (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [gram_const, hX, add_smul, one_smul]
  have hinv : (gram X (fun _ ↦ l))⁻¹ = (1 + l)⁻¹ • (1 : Matrix (Fin p) (Fin p) ℝ) :=
    inv_eq_right_inv <| by rw [hG, smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hl, one_smul]
  rw [fit_eq_shrink_ols_fit X y _ h h₀, hinv, hX, mul_one, smul_mulVec, one_mulVec]

/-- With orthonormal columns, OLS is `Xᵀy` and every positive scalar ridge is `Xᵀy / (1 + l)`. -/
theorem fitPositive_eq_smul_of_gram_eq_one (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (hX : OLS.gram X = 1) {l : ℝ} (hl : 0 < l) :
    fitPositive X y (fun _ ↦ l) (fun _ ↦ hl) = (1 + l)⁻¹ • (Xᵀ *ᵥ y) := by
  rw [fitPositive, fit_eq_smul_ols_fit_of_gram_eq_one X y hX (by positivity) _ (by simp [hX]),
    OLS.fit, hX, inv_one, one_mulVec]

/-! ## The ridge path -/

/-- The ridge coefficients as a function of a scalar penalty, with no side condition:
`(XᵀX + l I)⁻¹ Xᵀy`. (Mathlib's `⁻¹` is the zero matrix where the determinant vanishes.)
Where the regularized Gram matrix is nonsingular this is `fit`; at `l = 0` it is OLS. -/
def path (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (l : ℝ) : Fin p → ℝ :=
  (gram X (fun _ ↦ l))⁻¹ *ᵥ (Xᵀ *ᵥ y)

/-- Where the regularized Gram matrix is nonsingular, the path is the closed form `fit`. -/
theorem path_eq_fit (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (l : ℝ)
    (h : (gram X (fun _ ↦ l)).det ≠ 0) : path X y l = fit X y (fun _ ↦ l) h := rfl

/-- For a positive penalty the path is `fitPositive`: no side condition is left to discharge. -/
theorem path_eq_fitPositive (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) {l : ℝ} (hl : 0 < l) :
    path X y l = fitPositive X y (fun _ ↦ l) (fun _ ↦ hl) := rfl

/-- Every positive point of the path minimizes its ridge loss. -/
theorem path_isMinimizer (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) {l : ℝ} (hl : 0 < l) :
    IsMinimizer X y (fun _ ↦ l) (path X y l) :=
  fitPositive_minimizes X y _ (fun _ ↦ hl)

/-- The path starts at OLS: at `l = 0` it is the OLS fit, when `XᵀX` is nonsingular. -/
theorem path_zero (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (h : (OLS.gram X).det ≠ 0) :
    path X y 0 = OLS.fit X y h := by
  simp [path, OLS.fit, gram]

/-- The regularized Gram matrix `XᵀX + l I` depends continuously on the scalar penalty `l`. -/
theorem continuous_gram_const (X : Matrix (Fin n) (Fin p) ℝ) :
    Continuous fun l : ℝ ↦ gram X (fun _ ↦ l) := by
  unfold gram
  fun_prop

/-- The path is continuous wherever the regularized Gram matrix is nonsingular. -/
theorem continuousAt_path (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) {l : ℝ}
    (h : (gram X (fun _ ↦ l)).det ≠ 0) : ContinuousAt (path X y) l := by
  have hinv : ContinuousAt Inv.inv (gram X (fun _ ↦ l)) :=
    continuousAt_matrix_inv _ (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ h)
  exact (continuous_id.matrix_mulVec continuous_const).continuousAt.comp
    (hinv.comp (f := fun l ↦ gram X (fun _ ↦ l)) (continuous_gram_const X).continuousAt)

/-- For every design, the ridge path is continuous on `l > 0`. -/
theorem continuousOn_path (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) :
    ContinuousOn (path X y) (Set.Ioi 0) := fun _ hl ↦
  (continuousAt_path X y (gram_det_ne_zero X fun _ ↦ hl)).continuousWithinAt

/-- **Ridge → OLS as the penalty vanishes**, when the Gram matrix is nonsingular. -/
theorem tendsto_path_nhds_zero (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (h : (OLS.gram X).det ≠ 0) : Tendsto (path X y) (𝓝 0) (𝓝 (OLS.fit X y h)) := by
  simpa [path_zero X y h] using (continuousAt_path X y (l := 0) (by simpa [gram] using h)).tendsto

/-- The squared error of the zero coefficients is `‖y‖²`: the baseline every minimizer beats. -/
theorem ols_loss_zero (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) : OLS.loss X y 0 = y ⬝ᵥ y := by
  simp [OLS.loss, OLS.residual, OLS.predict]

/-- A ridge minimizer with scalar penalty `l > 0` has `‖w‖² ≤ ‖y‖² / l`: it can never do worse
than `w = 0`, whose loss is `‖y‖²`. -/
theorem sum_sq_le_of_isMinimizer (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) {l : ℝ} (hl : 0 < l)
    {w : Fin p → ℝ} (h : IsMinimizer X y (fun _ ↦ l) w) : ∑ j, w j ^ 2 ≤ y ⬝ᵥ y / l := by
  have h0 : OLS.loss X y w + l * ∑ j, w j ^ 2 ≤ y ⬝ᵥ y := by
    simpa [loss, penalty, Finset.mul_sum, ols_loss_zero] using h 0
  rw [le_div_iff₀ hl]
  linarith [OLS.loss_nonneg X y w]

/-- **Ridge → 0 as the penalty grows**: the squared norm of the ridge coefficients tends to
zero, for every design. -/
theorem tendsto_sum_sq_path_atTop (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) :
    Tendsto (fun l ↦ ∑ j, path X y l j ^ 2) atTop (𝓝 0) := by
  have hbound : ∀ᶠ l in atTop, ∑ j, path X y l j ^ 2 ≤ y ⬝ᵥ y / l := by
    filter_upwards [eventually_gt_atTop 0] with l hl
    exact sum_sq_le_of_isMinimizer X y hl (path_isMinimizer X y hl)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_nhds.div_atTop tendsto_id)
    (Eventually.of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hbound

end
end LeanLearn.Regression.Ridge
