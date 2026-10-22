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
noncomputable def smoothness : ℝ := (∑ r, ∑ i, P.x r i ^ 2) / m + P.ridge

/-- A per-sample bound on the squared feature norms bounds `Λ`. -/
theorem smoothness_le {R2 : ℝ} (hR2 : 0 ≤ R2) (h : ∀ r, ∑ i, P.x r i ^ 2 ≤ R2) :
    P.smoothness ≤ R2 + P.ridge := by
  rw [smoothness]
  gcongr
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simpa using hR2
  · rw [div_le_iff₀ (by exact_mod_cast hm)]
    calc ∑ r, ∑ i, P.x r i ^ 2 ≤ ∑ _r : Fin m, R2 := sum_le_sum fun r _ ↦ h r
      _ = R2 * m := by simp [mul_comm]

/-- The residual `A θ - b`. -/
noncomputable abbrev res (θ : Vec ℝ (d + 1)) : Vec ℝ (d + 1) :=
  residual P.normalMatrix P.normalVector θ

theorem gdStep_eq (η : ℝ) (θ : Vec ℝ (d + 1)) :
    gdStep P.normalMatrix P.normalVector η θ = vadd θ (smul (-(2 * η)) (P.res θ)) :=
  vext fun i ↦ by simp [gdStep, vadd, smul]; ring

/-- One step changes the loss by exactly `-4η ‖r‖² + 4η² C(r)`, `r = A θ - b`. -/
theorem loss_gdStep (η : ℝ) (θ : Vec ℝ (d + 1)) :
    P.loss (gdStep P.normalMatrix P.normalVector η θ) =
      P.loss θ - 4 * η * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 +
        4 * η ^ 2 * P.curvature (P.res θ) := by
  rw [gdStep_eq, loss_add, curvature_smul]
  simp only [smul_getElem]
  have : ∑ i : Fin (d + 1), (P.res θ)[i] * (-(2 * η) * (P.res θ)[i]) =
      -(2 * η) * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun i _ ↦ by ring
  rw [this]
  ring

/-- **Sufficient decrease**: with `0 ≤ η` and `2ηΛ ≤ 1`, a step lowers the loss by at
least `2η ‖A θ - b‖²`. -/
theorem loss_gdStep_le {η : ℝ} (hη : 0 ≤ η) (hstep : 2 * η * P.smoothness ≤ 1)
    (θ : Vec ℝ (d + 1)) :
    P.loss (gdStep P.normalMatrix P.normalVector η θ) ≤
      P.loss θ - 2 * η * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 := by
  rw [loss_gdStep]
  have hC := P.curvature_le (P.res θ)
  have hN : 0 ≤ ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have h1 : 4 * η ^ 2 * P.curvature (P.res θ) ≤
      4 * η ^ 2 * (P.smoothness * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2) :=
    mul_le_mul_of_nonneg_left hC (by positivity)
  have h2 : 2 * η * (2 * η * P.smoothness) * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 ≤
      2 * η * 1 * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 := by gcongr
  nlinarith [h1, h2]

/-- `‖(θ - 2η r) - u‖² = ‖θ - u‖² - 4η ⟪r, θ - u⟫ + 4η² ‖r‖²`. -/
theorem dist_gdStep (η : ℝ) (θ u : Vec ℝ (d + 1)) :
    ∑ i : Fin (d + 1), ((gdStep P.normalMatrix P.normalVector η θ)[i] - u[i]) ^ 2 =
      ∑ i : Fin (d + 1), (θ[i] - u[i]) ^ 2 -
        4 * η * ∑ i : Fin (d + 1), (P.res θ)[i] * (θ[i] - u[i]) +
        4 * η ^ 2 * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 := by
  rw [gdStep_eq]
  simp only [vadd_getElem, smul_getElem, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ by ring

/-- **Progress towards any point**: `2η (L θ' - L u) ≤ ‖θ - u‖² - ‖θ' - u‖²`. -/
theorem loss_gdStep_progress (hridge : 0 ≤ P.ridge) {η : ℝ} (hη : 0 ≤ η)
    (hstep : 2 * η * P.smoothness ≤ 1) (θ u : Vec ℝ (d + 1)) :
    2 * η * (P.loss (gdStep P.normalMatrix P.normalVector η θ) - P.loss u) ≤
      ∑ i : Fin (d + 1), (θ[i] - u[i]) ^ 2 -
        ∑ i : Fin (d + 1), ((gdStep P.normalMatrix P.normalVector η θ)[i] - u[i]) ^ 2 := by
  have hdec := P.loss_gdStep_le hη hstep θ
  have hconv := P.loss_ge_tangent hridge θ u
  rw [P.dist_gdStep η θ u]
  have hflip : ∑ i : Fin (d + 1), (P.res θ)[i] * (u[i] - θ[i]) =
      -∑ i : Fin (d + 1), (P.res θ)[i] * (θ[i] - u[i]) := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ ↦ by ring
  rw [hflip] at hconv
  have key : P.loss (gdStep P.normalMatrix P.normalVector η θ) - P.loss u ≤
      2 * ∑ i : Fin (d + 1), (P.res θ)[i] * (θ[i] - u[i]) -
        2 * η * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 := by linarith
  have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * η)
  nlinarith [this]

/-- After `k` steps from `θ₀`: `2ηk (L θₖ - L u) + ‖θₖ - u‖² ≤ ‖θ₀ - u‖²`. -/
theorem gd_invariant (hridge : 0 ≤ P.ridge) {η : ℝ} (hη : 0 ≤ η)
    (hstep : 2 * η * P.smoothness ≤ 1) (θ₀ u : Vec ℝ (d + 1)) (k : ℕ) :
    2 * η * k * (P.loss ((gdStep P.normalMatrix P.normalVector η)^[k] θ₀) - P.loss u) +
        ∑ i : Fin (d + 1), (((gdStep P.normalMatrix P.normalVector η)^[k] θ₀)[i] - u[i]) ^ 2 ≤
      ∑ i : Fin (d + 1), (θ₀[i] - u[i]) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set θ := (gdStep P.normalMatrix P.normalVector η)^[k] θ₀
    have hprog := P.loss_gdStep_progress hridge hη hstep θ u
    have hmono : P.loss (gdStep P.normalMatrix P.normalVector η θ) ≤ P.loss θ := by
      have := P.loss_gdStep_le hη hstep θ
      have : 0 ≤ 2 * η * ∑ i : Fin (d + 1), (P.res θ)[i] ^ 2 :=
        mul_nonneg (by positivity) (sum_nonneg fun _ _ ↦ sq_nonneg _)
      linarith
    have hk : 0 ≤ 2 * η * (k : ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left (sub_le_sub_right hmono (P.loss u)) hk
    push_cast
    nlinarith [h1, hprog, ih]

/-- Gradient descent never increases the loss, under the step-size condition. -/
theorem loss_gradientDescent_antitone {η : ℝ} (hη : 0 ≤ η) (hstep : 2 * η * P.smoothness ≤ 1) :
    Antitone fun k ↦ P.loss (gradientDescent P.normalMatrix P.normalVector η k) := by
  refine antitone_nat_of_succ_le fun k ↦ ?_
  simp only [gradientDescent]
  rw [Function.iterate_succ_apply']
  have := P.loss_gdStep_le hη hstep ((gdStep P.normalMatrix P.normalVector η)^[k] vzero)
  have : 0 ≤ 2 * η * ∑ i : Fin (d + 1),
      (P.res ((gdStep P.normalMatrix P.normalVector η)^[k] vzero))[i] ^ 2 :=
    mul_nonneg (by positivity) (sum_nonneg fun _ _ ↦ sq_nonneg _)
  linarith

/-- **The rate, multiplied out**: `2ηk (L θₖ - L u) ≤ ‖u‖²`. -/
theorem loss_gradientDescent_mul_le (hridge : 0 ≤ P.ridge) {η : ℝ} (hη : 0 ≤ η)
    (hstep : 2 * η * P.smoothness ≤ 1) (k : ℕ) (u : Vec ℝ (d + 1)) :
    2 * η * k * (P.loss (gradientDescent P.normalMatrix P.normalVector η k) - P.loss u) ≤
      ∑ i : Fin (d + 1), u[i] ^ 2 := by
  have h := P.gd_invariant hridge hη hstep vzero u k
  simp only [vzero_getElem, zero_sub, neg_sq] at h
  have : 0 ≤ ∑ i : Fin (d + 1),
      (((gdStep P.normalMatrix P.normalVector η)^[k] vzero)[i] - u[i]) ^ 2 :=
    sum_nonneg fun _ _ ↦ sq_nonneg _
  simp only [gradientDescent]
  linarith

/-- **Gradient descent converges at rate `O(1/k)`**: after `k ≥ 1` steps from `θ = 0`,
`L(θₖ) ≤ L(u) + ‖u‖² / (2ηk)` for every parameter vector `u`. -/
theorem loss_gradientDescent_le (hridge : 0 ≤ P.ridge) {η : ℝ} (hη : 0 < η)
    (hstep : 2 * η * P.smoothness ≤ 1) {k : ℕ} (hk : 0 < k) (u : Vec ℝ (d + 1)) :
    P.loss (gradientDescent P.normalMatrix P.normalVector η k) ≤
      P.loss u + (∑ i : Fin (d + 1), u[i] ^ 2) / (2 * η * k) := by
  have h := P.loss_gradientDescent_mul_le hridge hη.le hstep k u
  have hpos : 0 < 2 * η * (k : ℝ) := by positivity
  rw [← sub_le_iff_le_add', le_div_iff₀ hpos, mul_comm]
  exact h

/-- **Excess loss at most `ε`**: if `B ≤ 2ηkε`, the loss after `k ≥ 1` steps exceeds that of
every `u` with `‖u‖² ≤ B` by at most `ε`. -/
theorem loss_gradientDescent_le_add (hridge : 0 ≤ P.ridge) {η : ℝ} (hη : 0 < η)
    (hstep : 2 * η * P.smoothness ≤ 1) {k : ℕ} (hk : 0 < k) {B ε : ℝ}
    (hB : B ≤ 2 * η * k * ε) (u : Vec ℝ (d + 1)) (hu : ∑ i : Fin (d + 1), u[i] ^ 2 ≤ B) :
    P.loss (gradientDescent P.normalMatrix P.normalVector η k) ≤ P.loss u + ε := by
  have h := P.loss_gradientDescent_mul_le hridge hη.le hstep k u
  have hpos : 0 < 2 * η * (k : ℝ) := by positivity
  by_contra hcon
  push Not at hcon
  have := mul_lt_mul_of_pos_left (show ε < P.loss (gradientDescent P.normalMatrix
    P.normalVector η k) - P.loss u by linarith) hpos
  linarith

end Problem

end LeanLearn.Regression
