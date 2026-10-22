/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/

module

public import LeanSMILES.Proofs.ML.LeastSquares

/-!
# Gradient descent — the `O(1/k)` rate

Write `xᵢ` for `augment data.X[i]`, `L θ = mse (ofParams θ) data` for the loss in
parameter space, and `S = ∑ᵢ ‖xᵢ‖²`. Assume the step-size condition `2ηS ≤ m`, with
`η > 0`. (`S` bounds `m L/2`, where `L` is the smoothness constant, so this is the
classical `η ≤ 1/L`, in a form that can be checked.)

* **Convexity** (`mse_add_dot_le`): `L` lies above its tangent planes.
* **Sufficient decrease** (`mse_gdStep_le_sub`): a step lowers `L` by at least
  `(η/2) ‖∇L θ‖²`.
* **Progress towards any point** (`mse_gdStep_progress`): for every `u`,
  `2η (L θ' - L u) ≤ ‖θ - u‖² - ‖θ' - u‖²`.
* **The rate** (`mse_linRegGD_le`): after `k ≥ 1` iterations from `θ = 0`,
  `L θₖ ≤ L u + ‖u‖² / (2ηk)` for **every** linear model `u`. In particular `linRegGD`
  is within `‖θ*‖² / (2ηk)` of the least-squares optimum.

The step-size condition only involves the data through a bound on the feature norms:
`∀ i, ‖xᵢ‖² ≤ R²` and `2ηR² ≤ 1` imply it (`stepSize_condition_of_bound`). Molecular
representations come with such bounds (`Proofs/Chem/Representation.lean`), so the rate can
be established before training, from the hyperparameters alone.
-/

public section

namespace ML

open Primitives

variable {m n : ℕ} (data : Dataset ℝ m n)

/-- `∑ᵢ ‖xᵢ‖²` over the augmented samples. -/
noncomputable abbrev augmentedNormSqSum : ℝ := ∑ i : Fin m, normSq (augment data.X[i])

/-- A per-sample bound `‖xᵢ‖² ≤ R²` with `2ηR² ≤ 1` gives the step-size condition. -/
theorem stepSize_condition_of_bound {η R2 : ℝ} (hη : 0 ≤ η)
    (hR : ∀ i : Fin m, normSq (augment data.X[i]) ≤ R2) (h : 2 * η * R2 ≤ 1) :
    2 * η * augmentedNormSqSum data ≤ m := by
  have hsum : augmentedNormSqSum data ≤ m * R2 := by
    calc augmentedNormSqSum data ≤ ∑ _i : Fin m, R2 := Finset.sum_le_sum fun i _ => hR i
      _ = m * R2 := by simp
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc 2 * η * augmentedNormSqSum data ≤ 2 * η * (m * R2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = m * (2 * η * R2) := by ring
    _ ≤ m * 1 := mul_le_mul_of_nonneg_left h hm
    _ = m := mul_one _

/-! ## One step -/

/-- **Convexity**: `L θ + ⟪∇L θ, θ' - θ⟫ ≤ L θ'`. -/
theorem mse_add_dot_le (θ θ' : Vec ℝ (n + 1)) :
    mse (LinearModel.ofParams θ) data + dot (mseGrad data θ) (vsub θ' θ) ≤
      mse (LinearModel.ofParams θ') data := by
  have hstep := mse_step data θ (vsub θ' θ) 1
  have hθ' : vadd θ (smul 1 (vsub θ' θ)) = θ' := by
    ext j hj
    simp [vadd, smul, vsub]
  rw [hθ'] at hstep
  rw [hstep]
  have : 0 ≤ (1 : ℝ) ^ 2 * (∑ i : Fin m, dot (augment data.X[i]) (vsub θ' θ) ^ 2) / m :=
    div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => sq_nonneg _))
      (Nat.cast_nonneg m)
  linarith

/-- **Sufficient decrease**: with `0 ≤ η` and `2ηS ≤ m`, a gradient step lowers the loss
by at least `(η/2) ‖∇L θ‖²`. -/
theorem mse_gdStep_le_sub (θ : Vec ℝ (n + 1)) {η : ℝ} (hη : 0 ≤ η)
    (hstep : 2 * η * augmentedNormSqSum data ≤ m) :
    mse (LinearModel.ofParams (gdStep (mseObjective data) η θ)) data ≤
      mse (LinearModel.ofParams θ) data - η / 2 * normSq (mseGrad data θ) := by
  rw [mse_gdStep]
  have hS := sum_dot_sq_le data (mseGrad data θ)
  have hN := normSq_nonneg (mseGrad data θ)
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [Nat.cast_zero, div_zero]
    nlinarith [mul_nonneg hη hN]
  · have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have h1 := mul_le_mul_of_nonneg_left hS (sq_nonneg η)
    have h2 := mul_le_mul_of_nonneg_left hstep (mul_nonneg hη hN)
    have : η ^ 2 * (∑ i : Fin m, dot (augment data.X[i]) (mseGrad data θ) ^ 2) / m ≤
        η / 2 * normSq (mseGrad data θ) := by
      rw [div_le_iff₀ hm']
      nlinarith [h1, h2]
    linarith

/-- `‖(θ - η g) - u‖² = ‖θ - u‖² - 2η ⟪g, θ - u⟫ + η² ‖g‖²`. -/
theorem normSq_gdStep_vsub {k : ℕ} (obj : Objective ℝ k) (η : ℝ) (θ u : Vec ℝ k) :
    normSq (vsub (gdStep obj η θ) u) =
      normSq (vsub θ u) - 2 * η * dot (obj.grad θ) (vsub θ u) + η ^ 2 * normSq (obj.grad θ) := by
  simp only [normSq_eq_sum, dot_eq_sum, vsub, Fin.getElem_fin, Vector.getElem_ofFn,
    gdStep, smul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Progress towards any point**: one gradient step satisfies
`2η (L θ' - L u) ≤ ‖θ - u‖² - ‖θ' - u‖²`. -/
theorem mse_gdStep_progress (θ u : Vec ℝ (n + 1)) {η : ℝ} (hη : 0 ≤ η)
    (hstep : 2 * η * augmentedNormSqSum data ≤ m) :
    2 * η * (mse (LinearModel.ofParams (gdStep (mseObjective data) η θ)) data -
        mse (LinearModel.ofParams u) data) ≤
      normSq (vsub θ u) - normSq (vsub (gdStep (mseObjective data) η θ) u) := by
  have hdec := mse_gdStep_le_sub data θ hη hstep
  have hconv := mse_add_dot_le data θ u
  have hdist := normSq_gdStep_vsub (mseObjective data) η θ u
  rw [mseObjective_grad] at hdist
  rw [dot_vsub] at hconv
  rw [dot_vsub] at hdist
  have key : mse (LinearModel.ofParams (gdStep (mseObjective data) η θ)) data -
      mse (LinearModel.ofParams u) data ≤
      (dot (mseGrad data θ) θ - dot (mseGrad data θ) u) - η / 2 * normSq (mseGrad data θ) := by
    linarith
  have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * η)
  rw [hdist]
  nlinarith [this]

/-! ## The rate -/

/-- The telescoped invariant: after `k` steps from `θ₀`,
`2ηk (L θₖ - L u) + ‖θₖ - u‖² ≤ ‖θ₀ - u‖²`. -/
theorem gradientDescent_mse_invariant (u θ₀ : Vec ℝ (n + 1)) {η : ℝ} (hη : 0 ≤ η)
    (hstep : 2 * η * augmentedNormSqSum data ≤ m) (k : ℕ) :
    2 * η * k * (mse (LinearModel.ofParams (gradientDescent (mseObjective data) ⟨η, k⟩ θ₀)) data -
        mse (LinearModel.ofParams u) data) +
      normSq (vsub (gradientDescent (mseObjective data) ⟨η, k⟩ θ₀) u) ≤ normSq (vsub θ₀ u) := by
  have hstep' : η * augmentedNormSqSum data ≤ m := by
    have : 0 ≤ η * augmentedNormSqSum data :=
      mul_nonneg hη (Finset.sum_nonneg fun i _ => normSq_nonneg _)
    linarith
  induction k with
  | zero => simp
  | succ k ih =>
    rw [gradientDescent_succ]
    set θ := gradientDescent (mseObjective data) ⟨η, k⟩ θ₀
    have hprog := mse_gdStep_progress data θ u hη hstep
    have hmono := mse_gdStep_le data θ hη hstep'
    have hk : 0 ≤ 2 * η * (k : ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hmono (mse (LinearModel.ofParams u) data)) hk
    push_cast
    nlinarith [h1, hprog, ih]

/-- **Gradient descent converges at rate `O(1/k)`.** With `η > 0` and `2ηS ≤ m`, after
`k` iterations `linRegGD` satisfies
`2ηk (mse θₖ - mse u) ≤ ‖u‖²` for every linear model `u`. -/
theorem mse_linRegGD_mul_le {η : ℝ} (hη : 0 ≤ η)
    (hstep : 2 * η * augmentedNormSqSum data ≤ m) (k : ℕ) (model : LinearModel ℝ n) :
    2 * η * k * (mse (linRegGD ⟨η, k⟩ data) data - mse model data) ≤ normSq model.toParams := by
  have h := gradientDescent_mse_invariant data model.toParams vzero hη hstep k
  have hv : vsub (vzero : Vec ℝ (n + 1)) model.toParams = smul (-1) model.toParams := by
    ext j hj
    simp [vsub, vzero, smul]
  rw [hv, normSq_smul, ofParams_toParams] at h
  have := normSq_nonneg (vsub (gradientDescent (mseObjective data) ⟨η, k⟩ vzero) model.toParams)
  simp only [linRegGD]
  linarith

/-- **Gradient descent converges at rate `O(1/k)`.** With `η > 0` and `2ηS ≤ m`, after
`k ≥ 1` iterations the training error of `linRegGD` is within `‖u‖² / (2ηk)` of the
training error of **every** linear model `u` (whose parameter vector `(w, b)` is
`u.toParams`). -/
theorem mse_linRegGD_le {η : ℝ} (hη : 0 < η)
    (hstep : 2 * η * augmentedNormSqSum data ≤ m) {k : ℕ} (hk : 0 < k)
    (model : LinearModel ℝ n) :
    mse (linRegGD ⟨η, k⟩ data) data ≤ mse model data + normSq model.toParams / (2 * η * k) := by
  have h := mse_linRegGD_mul_le data hη.le hstep k model
  have hpos : 0 < 2 * η * (k : ℝ) := by positivity
  rw [← sub_le_iff_le_add', le_div_iff₀ hpos, mul_comm]
  exact h

/-- **Excess error at most `ε`.** If `B ≤ 2ηkε` (with `k ≥ 1`), then after `k` iterations
the training error of `linRegGD` exceeds that of any linear model with `‖(w, b)‖² ≤ B` by
at most `ε`. Every hypothesis is about the hyperparameters, not the trained model. -/
theorem mse_linRegGD_le_add {η : ℝ} (hη : 0 < η)
    (hstep : 2 * η * augmentedNormSqSum data ≤ m) {k : ℕ} (hk : 0 < k) {B ε : ℝ}
    (hB : B ≤ 2 * η * k * ε) (model : LinearModel ℝ n) (hmodel : normSq model.toParams ≤ B) :
    mse (linRegGD ⟨η, k⟩ data) data ≤ mse model data + ε := by
  have h := mse_linRegGD_mul_le data hη.le hstep k model
  have hpos : 0 < 2 * η * (k : ℝ) := by positivity
  by_contra hcon
  push Not at hcon
  have := mul_lt_mul_of_pos_left (show ε < mse (linRegGD ⟨η, k⟩ data) data - mse model data by
    linarith) hpos
  linarith

end ML

end
