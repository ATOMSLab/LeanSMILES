/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
-/
module

public import LeanLearn.Proofs.Regression.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# LeanLearn.Proofs.Regression.GradientDescent

Gradient descent — the `O(1/k)` rate.

For a problem with ridge penalty `λ ≥ 0`, write `Λ = (1/m) ∑ᵣ ‖xᵣ‖² + λ` (`smoothness`) and
assume the step-size condition `2ηΛ ≤ 1` with `η > 0`.

* **Sufficient decrease** (`loss_gdStep_le`): a step lowers the loss by at least
  `2η ‖A θ - b‖²`, so the loss never increases (`loss_gradientDescent_antitone`).
* **Progress towards any point** (`loss_gdStep_progress`):
  `2η (L θ' - L u) ≤ ‖θ - u‖² - ‖θ' - u‖²`.
* **The rate** (`loss_gradientDescent_le`): after `k ≥ 1` steps from `θ = 0`,
  `L(θₖ) ≤ L(u) + ‖u‖² / (2ηk)` for **every** parameter vector `u`.

The condition only involves the data through a bound on the feature norms:
`‖xᵣ‖² ≤ R²` for every sample gives `Λ ≤ R² + λ` (`smoothness_le`), so
`2η (R² + λ) ≤ 1` can be checked before training.
-/

@[expose] public section

namespace LeanLearn.Regression

open Finset

namespace Problem

variable {m d : ℕ} (P : Problem ℝ m d)

/-- `Λ = (1/m) ∑ᵣ ‖xᵣ‖² + λ`, which bounds the curvature: `C(v) ≤ Λ ‖v‖²`. -/
noncomputable def smoothness : ℝ := (∑ r, ∑ i, P.feature r i ^ 2) / m + P.ridge

/-- A per-sample bound on the squared feature norms bounds `Λ`. -/
theorem smoothness_le {R2 : ℝ} (hR2 : 0 ≤ R2) (h : ∀ r, ∑ i, P.feature r i ^ 2 ≤ R2) :
    P.smoothness ≤ R2 + P.ridge := by
  rw [smoothness]
  gcongr
  -- `∑ᵣ ‖xᵣ‖² ≤ m R²`, and dividing by `m` keeps it below `R²` (for `m = 0` both sides are `0`)
  exact div_le_of_le_mul₀ (Nat.cast_nonneg m) hR2 <|
    (sum_le_sum fun r _ ↦ h r).trans_eq (by simp [mul_comm])

/-- The residual `A θ - b`. -/
noncomputable abbrev res (θ : Vec ℝ (d + 1)) : Vec ℝ (d + 1) :=
  residual P.normalMatrix P.normalVector θ

/-- A gradient step in the vector notation of `loss_add`: `θ' = θ + (-2η) (A θ - b)`. -/
theorem gdStep_eq (η : ℝ) (θ : Vec ℝ (d + 1)) :
    gdStep P.normalMatrix P.normalVector η θ = vadd θ (smul (-(2 * η)) (P.res θ)) :=
  vext fun i ↦ by grind [gdStep, vadd_getElem, smul_getElem]

/-- One step changes the loss by exactly `-4η ‖r‖² + 4η² C(r)`, `r = A θ - b`. -/
theorem loss_gdStep (η : ℝ) (θ : Vec ℝ (d + 1)) :
    P.loss (gdStep P.normalMatrix P.normalVector η θ) =
      P.loss θ - 4 * η * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 +
        4 * η ^ 2 * P.curvature (P.res θ) := by
  rw [gdStep_eq, loss_add, curvature_smul]
  -- pull `-2η` out of `⟪r, -2η r⟫` and read `rᵢ rᵢ` as `rᵢ²`
  simp only [smul_getElem, mul_left_comm _ (-(2 * η)), ← mul_sum, ← sq]
  ring

/-- **Sufficient decrease**: with `0 ≤ η` and `2ηΛ ≤ 1`, a step lowers the loss by at
least `2η ‖A θ - b‖²`. -/
theorem loss_gdStep_le {η : ℝ} (hη : 0 ≤ η) (hstep : 2 * η * P.smoothness ≤ 1)
    (θ : Vec ℝ (d + 1)) :
    P.loss (gdStep P.normalMatrix P.normalVector η θ) ≤
      P.loss θ - 2 * η * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 := by
  rw [loss_gdStep]
  have hC : P.curvature (P.res θ) ≤ P.smoothness * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 :=
    P.curvature_le (P.res θ)
  have hN : 0 ≤ η * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 := by positivity
  -- `4η² C(r) ≤ 4η² Λ ‖r‖² = 2η · (2ηΛ) · ‖r‖² ≤ 2η ‖r‖²`
  linarith [mul_le_mul_of_nonneg_left hC (by positivity : 0 ≤ 4 * η ^ 2),
    mul_le_mul_of_nonneg_right hstep hN]

-- One step never increases the loss: the decrease `2η ‖A θ - b‖²` of `loss_gdStep_le` is `≥ 0`.
private theorem loss_gdStep_le_loss {η : ℝ} (hη : 0 ≤ η) (hstep : 2 * η * P.smoothness ≤ 1)
    (θ : Vec ℝ (d + 1)) : P.loss (gdStep P.normalMatrix P.normalVector η θ) ≤ P.loss θ :=
  (P.loss_gdStep_le hη hstep θ).trans (sub_le_self _ (by positivity))

/-- `‖(θ - 2η r) - u‖² = ‖θ - u‖² - 4η ⟪r, θ - u⟫ + 4η² ‖r‖²`. -/
theorem dist_gdStep (η : ℝ) (θ u : Vec ℝ (d + 1)) :
    ∑ i : Fin (d + 1), ((gdStep P.normalMatrix P.normalVector η θ)[i] - u[i]) ^ 2 =
      ∑ i : Fin (d + 1), (θ[i] - u[i]) ^ 2 -
        4 * η * ∑ i : Fin (d + 1), (P.res θ)[i] * (θ[i] - u[i]) +
        4 * η ^ 2 * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 := by
  simp only [gdStep_eq, vadd_getElem, smul_getElem, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ by ring

/-- **Progress towards any point**: `2η (L θ' - L u) ≤ ‖θ - u‖² - ‖θ' - u‖²`. -/
theorem loss_gdStep_progress (hridge : 0 ≤ P.ridge) {η : ℝ} (hη : 0 ≤ η)
    (hstep : 2 * η * P.smoothness ≤ 1) (θ u : Vec ℝ (d + 1)) :
    2 * η * (P.loss (gdStep P.normalMatrix P.normalVector η θ) - P.loss u) ≤
      ∑ i : Fin (d + 1), (θ[i] - u[i]) ^ 2 -
        ∑ i : Fin (d + 1), ((gdStep P.normalMatrix P.normalVector η θ)[i] - u[i]) ^ 2 := by
  have hconv := P.tangent_le_loss hridge θ u
  rw [P.dist_gdStep η θ u]
  -- split `⟪r, θ - u⟫` and `⟪r, u - θ⟫` into `⟪r, θ⟫` and `⟪r, u⟫`, so both bounds share atoms
  simp only [mul_sub, sum_sub_distrib] at hconv ⊢
  -- `2η ≥ 0` times (sufficient decrease plus convexity: `L θ' - L u ≤ 2 ⟪r, θ - u⟫ - 2η ‖r‖²`)
  nlinarith [P.loss_gdStep_le hη hstep θ]

/-- After `k` steps from `θ₀`: `2ηk (L θₖ - L u) + ‖θₖ - u‖² ≤ ‖θ₀ - u‖²`. -/
theorem gd_invariant (hridge : 0 ≤ P.ridge) {η : ℝ} (hη : 0 ≤ η) (hstep : 2 * η * P.smoothness ≤ 1)
    (θ₀ u : Vec ℝ (d + 1)) (k : ℕ) :
    2 * η * k * (P.loss ((gdStep P.normalMatrix P.normalVector η)^[k] θ₀) - P.loss u) +
        ∑ i : Fin (d + 1), (((gdStep P.normalMatrix P.normalVector η)^[k] θ₀)[i] - u[i]) ^ 2 ≤
      ∑ i : Fin (d + 1), (θ₀[i] - u[i]) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set θ := (gdStep P.normalMatrix P.normalVector η)^[k] θ₀
    push_cast
    -- `2η(k+1) (L θ' - L u) ≤ 2ηk (L θ - L u) + 2η (L θ' - L u)` as `L θ' ≤ L θ` and `2ηk ≥ 0`
    linarith [mul_le_mul_of_nonneg_left (sub_le_sub_right (P.loss_gdStep_le_loss hη hstep θ)
      (P.loss u)) (by positivity : 0 ≤ 2 * η * k), P.loss_gdStep_progress hridge hη hstep θ u, ih]

/-- Gradient descent never increases the loss, under the step-size condition. -/
theorem loss_gradientDescent_antitone {η : ℝ} (hη : 0 ≤ η) (hstep : 2 * η * P.smoothness ≤ 1) :
    Antitone fun k ↦ P.loss (gradientDescent P.normalMatrix P.normalVector η k) := by
  refine antitone_nat_of_succ_le fun k ↦ ?_
  simp only [gradientDescent, Function.iterate_succ_apply']
  exact P.loss_gdStep_le_loss hη hstep _

/-- **The rate, multiplied out**: `2ηk (L θₖ - L u) ≤ ‖u‖²`. -/
theorem loss_gradientDescent_mul_le (hridge : 0 ≤ P.ridge) {η : ℝ} (hη : 0 ≤ η)
    (hstep : 2 * η * P.smoothness ≤ 1) (k : ℕ) (u : Vec ℝ (d + 1)) :
    2 * η * k * (P.loss (gradientDescent P.normalMatrix P.normalVector η k) - P.loss u) ≤
      ∑ i : Fin (d + 1), u[i] ^ 2 := by
  have h := P.gd_invariant hridge hη hstep vzero u k
  simp only [vzero_getElem, zero_sub, neg_sq] at h
  rw [gradientDescent]
  exact (le_add_of_nonneg_right (by positivity)).trans h

/-- **Gradient descent converges at rate `O(1/k)`**: after `k ≥ 1` steps from `θ = 0`,
`L(θₖ) ≤ L(u) + ‖u‖² / (2ηk)` for every parameter vector `u`. -/
theorem loss_gradientDescent_le (hridge : 0 ≤ P.ridge) {η : ℝ} (hη : 0 < η)
    (hstep : 2 * η * P.smoothness ≤ 1) {k : ℕ} (hk : 0 < k) (u : Vec ℝ (d + 1)) :
    P.loss (gradientDescent P.normalMatrix P.normalVector η k) ≤
      P.loss u + (∑ i : Fin (d + 1), u[i] ^ 2) / (2 * η * k) := by
  rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity), mul_comm]
  exact P.loss_gradientDescent_mul_le hridge hη.le hstep k u

/-- **Excess loss at most `ε`**: if `B ≤ 2ηkε`, the loss after `k ≥ 1` steps exceeds that of
every `u` with `‖u‖² ≤ B` by at most `ε`. -/
theorem loss_gradientDescent_le_add (hridge : 0 ≤ P.ridge) {η : ℝ} (hη : 0 < η)
    (hstep : 2 * η * P.smoothness ≤ 1) {k : ℕ} (hk : 0 < k) {B ε : ℝ} (hB : B ≤ 2 * η * k * ε)
    (u : Vec ℝ (d + 1)) (hu : ∑ i : Fin (d + 1), u[i] ^ 2 ≤ B) :
    P.loss (gradientDescent P.normalMatrix P.normalVector η k) ≤ P.loss u + ε := by
  refine (P.loss_gradientDescent_le hridge hη hstep hk u).trans (add_le_add_right ?_ _)
  rw [div_le_iff₀ (by positivity)]
  -- `‖u‖² ≤ B ≤ 2ηk ε`
  linarith

end Problem

end LeanLearn.Regression
