module

public import LeanLearn.Regression.OLS
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ridge regression: exact specification and correctness

`ρ j` is the penalty on coefficient `j`. Standard ridge uses `fun _ => λ`;
an explicit intercept can be exempted by setting its penalty to zero.
All optimization statements range over every real coefficient vector.
-/

@[expose] public section

namespace LeanLearn.Regression.Ridge

open Matrix
open scoped BigOperators Matrix
noncomputable section
variable {n p : ℕ}

/-- Weighted squared coefficient norm. -/
def penalty (ρ w : Fin p → ℝ) : ℝ := ∑ j, ρ j * w j ^ 2

/-- Sum of squared residuals plus a diagonal ridge penalty; no averaging. -/
def loss (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (ρ w : Fin p → ℝ) : ℝ := OLS.loss X y w + penalty ρ w

/-- Global optimality among all real coefficient vectors. -/
def IsMinimizer (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (ρ w : Fin p → ℝ) : Prop := ∀ v, loss X y ρ w ≤ loss X y ρ v

/-- Regularized Gram matrix. -/
def gram (X : Matrix (Fin n) (Fin p) ℝ) (ρ : Fin p → ℝ) :=
  OLS.gram X + diagonal ρ

/-- Ridge normal equations, valid also for zero penalties. -/
def NormalEquations (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (ρ w : Fin p → ℝ) : Prop := gram X ρ *ᵥ w = Xᵀ *ᵥ y

theorem loss_eq_sum (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (ρ w : Fin p → ℝ) :
    loss X y ρ w = (∑ i, (OLS.predict X w i - y i)^2) + ∑ j, ρ j * w j^2 := by
  rw [loss, OLS.loss_eq_sum, penalty]

theorem penalty_nonneg {ρ : Fin p → ℝ} (hρ : ∀ j, 0 ≤ ρ j) (w : Fin p → ℝ) :
    0 ≤ penalty ρ w := Finset.sum_nonneg fun j _ => mul_nonneg (hρ j) (sq_nonneg _)

theorem loss_nonneg (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    {ρ : Fin p → ℝ} (hρ : ∀ j, 0 ≤ ρ j) (w : Fin p → ℝ) : 0 ≤ loss X y ρ w :=
  add_nonneg (OLS.loss_nonneg X y w) (penalty_nonneg hρ w)

theorem normalEquations_iff (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (ρ w : Fin p → ℝ) : NormalEquations X y ρ w ↔
    Xᵀ *ᵥ OLS.residual X y w + diagonal ρ *ᵥ w = 0 := by
  simp only [NormalEquations, gram, add_mulVec, OLS.residual, OLS.predict,
    mulVec_sub, mulVec_mulVec, OLS.gram]
  constructor <;> intro h <;> ext j
  · have hj := congrFun h j
    simp only [Pi.add_apply] at hj
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    linarith
  · have hj := congrFun h j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at hj
    simp only [Pi.add_apply]
    linarith

/-- Quadratic increase in the objective for a coefficient perturbation. -/
def energy (X : Matrix (Fin n) (Fin p) ℝ) (ρ d : Fin p → ℝ) : ℝ :=
  OLS.predict X d ⬝ᵥ OLS.predict X d + penalty ρ d

theorem energy_nonneg (X : Matrix (Fin n) (Fin p) ℝ) {ρ : Fin p → ℝ}
    (hρ : ∀ j, 0 ≤ ρ j) (d : Fin p → ℝ) : 0 ≤ energy X ρ d :=
  add_nonneg (Finset.sum_nonneg fun _ _ => mul_self_nonneg _) (penalty_nonneg hρ d)

theorem energy_eq (X : Matrix (Fin n) (Fin p) ℝ) (ρ d : Fin p → ℝ) :
    energy X ρ d = d ⬝ᵥ (gram X ρ *ᵥ d) := by
  rw [energy, gram, add_mulVec, dotProduct_add]
  congr 1
  · rw [OLS.gram, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
      transpose_transpose]
    rfl
  · simp [penalty, mulVec_diagonal, dotProduct, pow_two, mul_left_comm]

/-- Exact objective expansion at a solution of the normal equations. -/
theorem loss_add_of_normalEquations (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (ρ : Fin p → ℝ) {w : Fin p → ℝ}
    (h : NormalEquations X y ρ w) (d : Fin p → ℝ) :
    loss X y ρ (w + d) = loss X y ρ w + energy X ρ d := by
  have hcross := congrArg (fun z => z ⬝ᵥ d) ((normalEquations_iff X y ρ w).mp h)
  simp only [add_dotProduct, zero_dotProduct] at hcross
  have hdot : (Xᵀ *ᵥ OLS.residual X y w) ⬝ᵥ d =
      OLS.residual X y w ⬝ᵥ OLS.predict X d := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, transpose_transpose,
      dotProduct_comm]
    rfl
  rw [hdot] at hcross
  have hp : penalty ρ (w + d) = penalty ρ w +
      2 * ((diagonal ρ *ᵥ w) ⬝ᵥ d) + penalty ρ d := by
    simp only [penalty, mulVec_diagonal, dotProduct, Pi.add_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [loss, OLS.loss, OLS.residual_add, add_dotProduct, dotProduct_add,
    hp, energy]
  rw [dotProduct_comm (OLS.predict X d) (OLS.residual X y w)]
  linarith

theorem normalEquations_minimize (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) {ρ : Fin p → ℝ} (hρ : ∀ j, 0 ≤ ρ j)
    {w : Fin p → ℝ} (h : NormalEquations X y ρ w) : IsMinimizer X y ρ w := by
  intro v
  have heq := loss_add_of_normalEquations X y ρ h (v - w)
  rw [add_sub_cancel] at heq
  have := energy_nonneg X hρ (v - w)
  linarith

/-- Closed-form exact algorithm with an explicit invertibility precondition. -/
def fit (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (ρ : Fin p → ℝ)
    (_h : (gram X ρ).det ≠ 0) : Fin p → ℝ := (gram X ρ)⁻¹ *ᵥ (Xᵀ *ᵥ y)

theorem fit_normalEquations (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (ρ : Fin p → ℝ) (h : (gram X ρ).det ≠ 0) : NormalEquations X y ρ (fit X y ρ h) := by
  unfold NormalEquations fit
  rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h), one_mulVec]

theorem fit_minimizes (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    {ρ : Fin p → ℝ} (hρ : ∀ j, 0 ≤ ρ j) (h : (gram X ρ).det ≠ 0) :
    IsMinimizer X y ρ (fit X y ρ h) :=
  normalEquations_minimize X y hρ (fit_normalEquations X y ρ h)

/-- Strictly positive penalties remove the rank requirement on the original design. -/
theorem gram_posDef (X : Matrix (Fin n) (Fin p) ℝ) {ρ : Fin p → ℝ}
    (hρ : ∀ j, 0 < ρ j) : (gram X ρ).PosDef := by
  have hX : (OLS.gram X).PosSemidef := by
    simpa [OLS.gram] using posSemidef_conjTranspose_mul_self X
  exact PosDef.posSemidef_add hX (PosDef.diagonal hρ)

theorem gram_det_ne_zero (X : Matrix (Fin n) (Fin p) ℝ) {ρ : Fin p → ℝ}
    (hρ : ∀ j, 0 < ρ j) : (gram X ρ).det ≠ 0 :=
  ((gram X ρ).isUnit_iff_isUnit_det.mp (gram_posDef X hρ).isUnit).ne_zero

/-- Ordinary positive ridge is defined for every design, even with fewer rows than columns. -/
def fitPositive (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (ρ : Fin p → ℝ) (hρ : ∀ j, 0 < ρ j) : Fin p → ℝ :=
  fit X y ρ (gram_det_ne_zero X hρ)

theorem fitPositive_minimizes (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (ρ : Fin p → ℝ) (hρ : ∀ j, 0 < ρ j) : IsMinimizer X y ρ (fitPositive X y ρ hρ) :=
  fit_minimizes X y (fun j => (hρ j).le) _

/-- Positive definiteness guarantees uniqueness, also for identifiable exempt-intercept models. -/
theorem normalEquations_unique (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (ρ : Fin p → ℝ) (hG : (gram X ρ).PosDef) {w v : Fin p → ℝ}
    (hw : NormalEquations X y ρ w) (hv : IsMinimizer X y ρ v) : v = w := by
  by_contra hne
  have hd : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < energy X ρ (v - w) := by
    rw [energy_eq]
    simpa using hG.dotProduct_mulVec_pos hd
  have heq := loss_add_of_normalEquations X y ρ hw (v - w)
  rw [add_sub_cancel] at heq
  have := hv w
  linarith

theorem fitPositive_unique (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (ρ : Fin p → ℝ) (hρ : ∀ j, 0 < ρ j) {w : Fin p → ℝ}
    (hw : IsMinimizer X y ρ w) : w = fitPositive X y ρ hρ :=
  normalEquations_unique X y ρ (gram_posDef X hρ) (fit_normalEquations X y ρ _) hw

/-- OLS is the zero-penalty special case. -/
@[simp] theorem loss_zero_penalty (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (w : Fin p → ℝ) : loss X y 0 w = OLS.loss X y w := by
  simp [loss, penalty]

@[simp] theorem normalEquations_zero_penalty (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (w : Fin p → ℝ) :
    NormalEquations X y 0 w ↔ OLS.NormalEquations X y w := by
  simp [NormalEquations, gram, OLS.normalEquations_iff]

/-- The exact closed-form formula reduces to OLS at zero penalty. -/
theorem fit_zero_penalty (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (h : (OLS.gram X).det ≠ 0) :
    fit X y 0 (by simpa [gram] using h) = OLS.fit X y h := by
  simp [fit, gram, OLS.fit]

/-- Positive ridge has exactly one real global minimizer for every design. -/
theorem exists_unique_minimizer (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (ρ : Fin p → ℝ) (hρ : ∀ j, 0 < ρ j) : ∃! w, IsMinimizer X y ρ w := by
  exact ⟨fitPositive X y ρ hρ, fitPositive_minimizes X y ρ hρ,
    fun w hw => fitPositive_unique X y ρ hρ hw⟩

/-- Augmented design used by the numerical QR implementation. -/
def augmentedDesign (X : Matrix (Fin n) (Fin p) ℝ) (ρ : Fin p → ℝ) :
    Matrix (Fin (n + p)) (Fin p) ℝ :=
  Fin.addCases X (diagonal fun j => Real.sqrt (ρ j))

/-- Targets of the penalty observations are zero. -/
def augmentedTargets (y : Fin n → ℝ) : Fin (n + p) → ℝ :=
  Fin.addCases y (fun _ => 0)

/-- Ridge is exactly least squares on the augmented design, before rounding. -/
theorem augmented_loss (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    {ρ : Fin p → ℝ} (hρ : ∀ j, 0 ≤ ρ j) (w : Fin p → ℝ) :
    OLS.loss (augmentedDesign X ρ) (augmentedTargets y) w = loss X y ρ w := by
  rw [OLS.loss_eq_sum, Fin.sum_univ_add, loss_eq_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp [OLS.predict, mulVec, dotProduct, augmentedDesign, augmentedTargets]
  · apply Finset.sum_congr rfl
    intro j _
    simp [OLS.predict, mulVec, dotProduct, augmentedDesign, augmentedTargets,
      diagonal, mul_pow, Real.sq_sqrt (hρ j)]

end
end LeanLearn.Regression.Ridge
