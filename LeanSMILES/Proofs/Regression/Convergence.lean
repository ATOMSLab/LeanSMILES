/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
import LeanSMILES.Proofs.Regression.Minimization
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# LeanSMILES.Proofs.Regression.Convergence

The solvers converge to the minimizer, and the loss to the minimum.

`Minimization.lean` identifies the target — a minimizer `θ*` of the ridge loss, unique
when `λ > 0` or under diagonal dominance — and the rate theorems bound how far each
iterate is from it. Together they give limits:

* **Gradient descent** (`2ηΛ ≤ 1`, `η > 0`). For any minimizer, the loss converges to the
  minimum at rate `‖θ*‖² / (2ηk)` (`loss_gradientDescent_sub_le`,
  `tendsto_loss_gradientDescent`). With `λ > 0` the iterates converge to the unique
  minimizer, `‖θₖ - θ*‖² ≤ ‖θ*‖² / (2ηkλ)` (`dist_gradientDescent_le`,
  `tendsto_gradientDescent`).
* **Jacobi and Gauss–Seidel** (weighted diagonal dominance). The iterates converge
  linearly to the minimizer, coordinate by coordinate, and the loss to the minimum
  (`tendsto_jacobi`, `tendsto_gaussSeidel`).

So each solver, run long enough under its condition, *finds the minimizer*: the
optimization problem and the iteration have the same answer.
-/

namespace LeanSMILES.Regression

open Finset Filter Topology

/-! ## Limits from bounds -/

/-- A sequence with `|xₖ - a| ≤ ρᵏ C`, `0 ≤ ρ < 1`, converges to `a`. -/
theorem tendsto_of_abs_sub_le_geometric {x : ℕ → ℝ} {a ρ C : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ k, |x k - a| ≤ ρ ^ k * C) : Tendsto x atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => by simpa using h k) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const C

/-- A sequence with `(xₖ - a)² → 0` converges to `a`. -/
theorem tendsto_of_sq_sub_tendsto_zero {x : ℕ → ℝ} {a : ℝ}
    (h : Tendsto (fun k => (x k - a) ^ 2) atTop (𝓝 0)) : Tendsto x atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto 0).comp h
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using this

namespace Problem

variable {m d : ℕ} (P : Problem ℝ m d)

/-! ## Gradient descent -/

section GradientDescent

variable {η : ℝ}

/-- **Rate to the minimum**: `0 ≤ L(θₖ) - L(θ*) ≤ ‖θ*‖² / (2ηk)` for any minimizer `θ*`. -/
theorem loss_gradientDescent_sub_le (hridge : 0 ≤ P.ridge) (hη : 0 < η)
    (hstep : 2 * η * P.smoothness ≤ 1) {k : ℕ} (hk : 0 < k) {θs : Vec ℝ (d + 1)}
    (hmin : P.IsMinimizer θs) :
    0 ≤ P.loss (gradientDescent P.normalMatrix P.normalVector η k) - P.loss θs ∧
      P.loss (gradientDescent P.normalMatrix P.normalVector η k) - P.loss θs ≤
        (∑ i : Fin (d + 1), θs[i] ^ 2) / (2 * η * k) :=
  ⟨sub_nonneg.mpr (hmin _), by
    have := P.loss_gradientDescent_le hridge hη hstep hk θs
    linarith⟩

/-- **Rate of the iterates** (`λ > 0`): `‖θₖ - θ*‖² ≤ ‖θ*‖² / (2ηkλ)`. -/
theorem dist_gradientDescent_le (hridge : 0 < P.ridge) (hη : 0 < η)
    (hstep : 2 * η * P.smoothness ≤ 1) {k : ℕ} (hk : 0 < k) {θs : Vec ℝ (d + 1)}
    (hmin : P.IsMinimizer θs) :
    ∑ i : Fin (d + 1), ((gradientDescent P.normalMatrix P.normalVector η k)[i] - θs[i]) ^ 2 ≤
      (∑ i : Fin (d + 1), θs[i] ^ 2) / (2 * η * k) / P.ridge := by
  rw [le_div_iff₀ hridge, mul_comm]
  exact (P.ridge_mul_dist_le hridge.le hmin _).trans
    (P.loss_gradientDescent_sub_le hridge.le hη hstep hk hmin).2

/-- **The loss of gradient descent converges to the minimum.** -/
theorem tendsto_loss_gradientDescent (hridge : 0 ≤ P.ridge) (hη : 0 < η)
    (hstep : 2 * η * P.smoothness ≤ 1) {θs : Vec ℝ (d + 1)} (hmin : P.IsMinimizer θs) :
    Tendsto (fun k => P.loss (gradientDescent P.normalMatrix P.normalVector η k)) atTop
      (𝓝 (P.loss θs)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  set C := (∑ i : Fin (d + 1), θs[i] ^ 2) / (2 * η)
  refine squeeze_zero' (Eventually.of_forall fun k => sub_nonneg.mpr (hmin _))
    ((eventually_gt_atTop 0).mono fun k hk => ?_) (tendsto_const_div_atTop_nhds_zero_nat C)
  calc _ ≤ (∑ i : Fin (d + 1), θs[i] ^ 2) / (2 * η * k) :=
        (P.loss_gradientDescent_sub_le hridge hη hstep hk hmin).2
    _ = C / k := by rw [div_div]

/-- **Gradient descent converges to the minimizer** (`λ > 0`), coordinate by coordinate. -/
theorem tendsto_gradientDescent (hridge : 0 < P.ridge) (hη : 0 < η)
    (hstep : 2 * η * P.smoothness ≤ 1) {θs : Vec ℝ (d + 1)} (hmin : P.IsMinimizer θs)
    (i : Fin (d + 1)) :
    Tendsto (fun k => (gradientDescent P.normalMatrix P.normalVector η k)[i]) atTop
      (𝓝 θs[i]) := by
  refine tendsto_of_sq_sub_tendsto_zero ?_
  have hloss := (P.tendsto_loss_gradientDescent hridge.le hη hstep hmin).sub_const (P.loss θs)
  rw [sub_self] at hloss
  refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) (by simpa using hloss.div_const P.ridge)
  rw [le_div_iff₀ hridge, mul_comm]
  calc P.ridge * ((gradientDescent P.normalMatrix P.normalVector η k)[i] - θs[i]) ^ 2
      ≤ P.ridge * ∑ j : Fin (d + 1),
          ((gradientDescent P.normalMatrix P.normalVector η k)[j] - θs[j]) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (single_le_sum (f := fun j : Fin (d + 1) =>
            ((gradientDescent P.normalMatrix P.normalVector η k)[j] - θs[j]) ^ 2)
            (fun _ _ => sq_nonneg _) (mem_univ i)) hridge.le
    _ ≤ _ := P.ridge_mul_dist_le hridge.le hmin _

/-- With `λ > 0`, gradient descent finds the minimizer, which exists and is unique. -/
theorem gradientDescent_finds_minimizer (hridge : 0 < P.ridge) (hη : 0 < η)
    (hstep : 2 * η * P.smoothness ≤ 1) :
    ∃ θs : Vec ℝ (d + 1), P.IsMinimizer θs ∧
      (∀ θ, P.IsMinimizer θ → θ = θs) ∧
      ∀ i : Fin (d + 1), Tendsto (fun k => (gradientDescent P.normalMatrix P.normalVector η k)[i])
        atTop (𝓝 θs[i]) := by
  obtain ⟨θs, hmin⟩ := P.exists_isMinimizer hridge
  exact ⟨θs, hmin, fun θ h => P.isMinimizer_unique hridge h hmin,
    P.tendsto_gradientDescent hridge hη hstep hmin⟩

end GradientDescent

/-! ## Jacobi and Gauss–Seidel -/

section Iterative

variable {w : Vec ℝ (d + 1)} {ρ : ℝ}

/-- A weight-scaled bound on a vector: `|θ*ⱼ| ≤ M wⱼ` with `M = ∑ⱼ |θ*ⱼ| / wⱼ`. -/
theorem abs_le_weightedSum (hw : ∀ j : Fin (d + 1), 0 < w[j]) (θs : Vec ℝ (d + 1))
    (j : Fin (d + 1)) : |θs[j]| ≤ (∑ l : Fin (d + 1), |θs[l]| / w[l]) * w[j] := by
  rw [← div_le_iff₀ (hw j)]
  exact single_le_sum (f := fun l : Fin (d + 1) => |θs[l]| / w[l])
    (fun l _ => div_nonneg (abs_nonneg _) (hw l).le) (mem_univ j)

/-- The loss after a sequence of iterates converging geometrically to a minimizer converges
to the minimum. -/
theorem tendsto_loss_of_geometric (hridge : 0 ≤ P.ridge) (hw : ∀ j : Fin (d + 1), 0 ≤ w[j])
    {θs : Vec ℝ (d + 1)}
    (hsol : ∀ i : Fin (d + 1), (matVec P.normalMatrix θs)[i] = P.normalVector[i])
    {ρ M : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 0 ≤ M) (θ : ℕ → Vec ℝ (d + 1))
    (h : ∀ k (i : Fin (d + 1)), |(θ k)[i] - θs[i]| ≤ ρ ^ k * M * w[i]) :
    Tendsto (fun k => P.loss (θ k)) atTop (𝓝 (P.loss θs)) := by
  have hmin : P.IsMinimizer θs := (P.isMinimizer_iff_residual_eq_zero hridge θs).mpr fun i => by
    change (residual P.normalMatrix P.normalVector θs)[i] = 0
    rw [residual, vsub_getElem, hsol i, sub_self]
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero (fun k => sub_nonneg.mpr (hmin _)) (fun k => ?_)
    (g := fun k => (ρ ^ k * M) ^ 2 * weightedMass P.normalMatrix w) ?_
  · have := P.loss_le_of_near_solution hridge hw hsol (mul_nonneg (pow_nonneg hρ0 k) hM) (θ k)
      (h k) θs
    linarith
  · have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have := ((hpow.mul_const M).pow 2).mul_const (weightedMass P.normalMatrix w)
    simpa using this

/-- **Jacobi converges to the minimizer**, and the loss to the minimum, under weighted
diagonal dominance. -/
theorem tendsto_jacobi (hridge : 0 ≤ P.ridge) (hdd : DiagDominant P.normalMatrix w ρ) :
    ∃ θs : Vec ℝ (d + 1), P.IsMinimizer θs ∧
      (∀ i : Fin (d + 1), Tendsto (fun k => (jacobi P.normalMatrix P.normalVector k)[i]) atTop
        (𝓝 θs[i])) ∧
      Tendsto (fun k => P.loss (jacobi P.normalMatrix P.normalVector k)) atTop
        (𝓝 (P.loss θs)) := by
  obtain ⟨θs, hsol, hmin⟩ := P.exists_isMinimizer_of_diagDominant hridge hdd
  set M := ∑ l : Fin (d + 1), |θs[l]| / w[l]
  have hM : 0 ≤ M := sum_nonneg fun l _ => div_nonneg (abs_nonneg _) (hdd.weight_pos l).le
  have h₀ : ∀ j : Fin (d + 1), |(vzero : Vec ℝ (d + 1))[j] - θs[j]| ≤ M * w[j] := fun j => by
    rw [vzero_getElem, zero_sub, abs_neg]
    exact abs_le_weightedSum hdd.weight_pos θs j
  have hb := jacobi_iterate_bound hdd hsol hM vzero h₀
  refine ⟨θs, hmin, fun i => ?_, ?_⟩
  · exact tendsto_of_abs_sub_le_geometric hdd.ratio_nonneg hdd.ratio_lt_one
      (C := M * w[i]) fun k => by rw [← mul_assoc]; exact hb k i
  · exact P.tendsto_loss_of_geometric hridge (fun j => (hdd.weight_pos j).le) hsol
      hdd.ratio_nonneg hdd.ratio_lt_one hM _ hb

/-- **Gauss–Seidel converges to the minimizer**, and the loss to the minimum, under
weighted diagonal dominance. -/
theorem tendsto_gaussSeidel (hridge : 0 ≤ P.ridge) (hdd : DiagDominant P.normalMatrix w ρ) :
    ∃ θs : Vec ℝ (d + 1), P.IsMinimizer θs ∧
      (∀ i : Fin (d + 1), Tendsto (fun k => (gaussSeidel P.normalMatrix P.normalVector k)[i])
        atTop (𝓝 θs[i])) ∧
      Tendsto (fun k => P.loss (gaussSeidel P.normalMatrix P.normalVector k)) atTop
        (𝓝 (P.loss θs)) := by
  obtain ⟨θs, hsol, hmin⟩ := P.exists_isMinimizer_of_diagDominant hridge hdd
  set M := ∑ l : Fin (d + 1), |θs[l]| / w[l]
  have hM : 0 ≤ M := sum_nonneg fun l _ => div_nonneg (abs_nonneg _) (hdd.weight_pos l).le
  have h₀ : ∀ j : Fin (d + 1), |(vzero : Vec ℝ (d + 1))[j] - θs[j]| ≤ M * w[j] := fun j => by
    rw [vzero_getElem, zero_sub, abs_neg]
    exact abs_le_weightedSum hdd.weight_pos θs j
  have hb := gaussSeidel_iterate_bound hdd hsol hM vzero h₀
  refine ⟨θs, hmin, fun i => ?_, ?_⟩
  · exact tendsto_of_abs_sub_le_geometric hdd.ratio_nonneg hdd.ratio_lt_one
      (C := M * w[i]) fun k => by rw [← mul_assoc]; exact hb k i
  · exact P.tendsto_loss_of_geometric hridge (fun j => (hdd.weight_pos j).le) hsol
      hdd.ratio_nonneg hdd.ratio_lt_one hM _ hb

end Iterative

end Problem

end LeanSMILES.Regression
