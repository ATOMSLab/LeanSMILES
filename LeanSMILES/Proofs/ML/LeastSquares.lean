module

public import LeanSMILES.Proofs.ML.Basic
public import LeanSMILES.Proofs.LinSolve

/-!
# Least squares — correctness and comparisons

Theorems over `ℝ` about `mse`, `olsFit` and `linRegGD`. Write `xᵢ` for row `i` of the
augmented design matrix (`augment data.X[i]`, the features with a `1` appended) and
`L θ = mse (ofParams θ) data` for the loss in parameter space.

* **The loss is an exact quadratic** (`mse_step`): moving from `θ` by `t • d` changes the
  loss by `t ⟪∇L θ, d⟫ + t² (1/m) ∑ᵢ ⟪xᵢ, d⟫²`. So `mseGrad` is the gradient of `L`.
* **Optimality** (`mse_le_of_grad_eq_zero`, `grad_eq_zero_of_isMinimizer`): `∇L θ = 0`
  exactly when `θ` minimises `L` over all linear models.
* **Normal equations** (`mseGrad_eq_normal`): `∇L θ = (2/m) (XₐᵀXₐ θ - Xₐᵀ y)`, so `olsFit`
  is optimal whenever `linSolve` solved its system (`olsFit_optimal`), and in particular no
  worse than gradient descent or the perceptron (`mse_olsFit_le_linRegGD`, …). Since
  Gauss–Jordan elimination is correct (`Proofs/LinSolve.lean`), this holds whenever the
  augmented features are linearly independent (`olsFit_optimal_of_fullColumnRank`).
* **Gradient descent** (`gdStep_eq_self_iff`, `mse_gdStep_le`): for `η ≠ 0` its fixed points
  are exactly the minimisers, and with `0 ≤ η ≤ m / ∑ᵢ ‖xᵢ‖²` the loss never increases
  (`mse_linRegGD_antitone`).
-/

public section

namespace ML

open Primitives

/-! ## The loss is an exact quadratic -/

section Loss

variable {m n : ℕ} (data : Dataset ℝ m n)

theorem mseObjective_grad : (mseObjective data).grad = mseGrad data := rfl

theorem mseObjective_loss (θ : Vec ℝ (n + 1)) :
    (mseObjective data).loss θ = mse (LinearModel.ofParams θ) data := rfl

/-- `L θ = (1/m) ∑ᵢ (⟪xᵢ, θ⟫ - yᵢ)²`. -/
theorem mse_ofParams (θ : Vec ℝ (n + 1)) :
    mse (LinearModel.ofParams θ) data =
      (∑ i : Fin m, (dot (augment data.X[i]) θ - data.y[i]) ^ 2) / m := by
  simp only [mse, normSq_eq_sum, residuals, Fin.getElem_fin, Vector.getElem_ofFn, score_ofParams,
    fromNat_real]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [dot_comm]

/-- `(∇L θ)ⱼ = (2/m) ∑ᵢ (xᵢ)ⱼ (⟪xᵢ, θ⟫ - yᵢ)`. -/
theorem mseGrad_getElem (θ : Vec ℝ (n + 1)) (j : Fin (n + 1)) :
    (mseGrad data θ)[j] =
      2 / m * ∑ i : Fin m, (augment data.X[i])[j] * (dot (augment data.X[i]) θ - data.y[i]) := by
  simp only [mseGrad, mseGradAux, smul, matVec, vsub, transpose, Fin.getElem_fin,
    Vector.getElem_ofFn,
    augmentMat_getElem, fromNat_real, dot_eq_sum, Nat.cast_ofNat]

/-- `⟪∇L θ, d⟫ = (2/m) ∑ᵢ (⟪xᵢ, θ⟫ - yᵢ) ⟪xᵢ, d⟫`. -/
theorem dot_mseGrad (θ d : Vec ℝ (n + 1)) :
    dot (mseGrad data θ) d =
      2 / m * ∑ i : Fin m, (dot (augment data.X[i]) θ - data.y[i]) * dot (augment data.X[i]) d := by
  rw [dot_eq_sum]
  simp only [mseGrad_getElem]
  exact sum_weighted_rows (fun i => augment data.X[i]) _ _ d

/-- **Exact second-order expansion** of the loss along a direction `d`:
`L (θ + t d) = L θ + t ⟪∇L θ, d⟫ + t² (1/m) ∑ᵢ ⟪xᵢ, d⟫²`. -/
theorem mse_step (θ d : Vec ℝ (n + 1)) (t : ℝ) :
    mse (LinearModel.ofParams (vadd θ (smul t d))) data =
      mse (LinearModel.ofParams θ) data + t * dot (mseGrad data θ) d +
        t ^ 2 * (∑ i : Fin m, dot (augment data.X[i]) d ^ 2) / m := by
  rw [mse_ofParams, mse_ofParams, dot_mseGrad]
  simp only [dot_vadd_smul]
  have h : ∀ i : Fin m,
      (dot (augment data.X[i]) θ + t * dot (augment data.X[i]) d - data.y[i]) ^ 2 =
        (dot (augment data.X[i]) θ - data.y[i]) ^ 2 +
          2 * t * ((dot (augment data.X[i]) θ - data.y[i]) * dot (augment data.X[i]) d) +
          t ^ 2 * dot (augment data.X[i]) d ^ 2 := fun i => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Loss

/-! ## Optimality: zero gradient ⟺ global minimum -/

section Optimality

variable {m n : ℕ} (data : Dataset ℝ m n)

/-- A parameter vector with zero gradient is a **global** minimiser: no linear model has a
smaller mean squared error. -/
theorem mse_le_of_grad_eq_zero (θ : Vec ℝ (n + 1))
    (hθ : ∀ j : Fin (n + 1), (mseGrad data θ)[j] = 0) (model : LinearModel ℝ n) :
    mse (LinearModel.ofParams θ) data ≤ mse model data := by
  rw [← ofParams_toParams model]
  have hstep := mse_step data θ (vsub model.toParams θ) 1
  have hθ' : vadd θ (smul 1 (vsub model.toParams θ)) = model.toParams := by
    ext j hj
    simp [vadd, smul, vsub]
  have hdot : dot (mseGrad data θ) (vsub model.toParams θ) = 0 := by
    rw [dot_eq_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [hθ j, zero_mul]
  rw [hθ', hdot] at hstep
  rw [hstep]
  have : 0 ≤ (1 : ℝ) ^ 2 * (∑ i : Fin m, dot (augment data.X[i]) (vsub model.toParams θ) ^ 2)
      / m :=
    div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => sq_nonneg _))
      (Nat.cast_nonneg m)
  linarith

/-- Conversely, a global minimiser has zero gradient. -/
theorem grad_eq_zero_of_isMinimizer (θ : Vec ℝ (n + 1))
    (hmin : ∀ θ' : Vec ℝ (n + 1),
      mse (LinearModel.ofParams θ) data ≤ mse (LinearModel.ofParams θ') data)
    (j : Fin (n + 1)) : (mseGrad data θ)[j] = 0 := by
  obtain ⟨g, hg⟩ : ∃ g, g = mseGrad data θ := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i : Fin m, dot (augment data.X[i]) g ^ 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = normSq g := ⟨_, rfl⟩
  have hc : 0 ≤ S / m :=
    div_nonneg (hS ▸ Finset.sum_nonneg fun i _ => sq_nonneg _) (Nat.cast_nonneg m)
  -- step against the gradient by `t = -a / (S/m + 1)`: the loss would drop by `(a/(S/m+1))²`
  have h := hmin (vadd θ (smul (-a / (S / m + 1)) g))
  rw [mse_step, ← hg, ← hS] at h
  have hdot : dot g g = a := ha.symm
  rw [hdot] at h
  have hc1 : 0 < S / m + 1 := by linarith
  have key : (-a / (S / m + 1)) * a + (-a / (S / m + 1)) ^ 2 * S / m =
      -(a / (S / m + 1)) ^ 2 := by
    field_simp
    ring
  have hsq : (a / (S / m + 1)) ^ 2 ≤ 0 := by linarith
  have ha0 : a = 0 := by
    have : a / (S / m + 1) = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp
      (le_antisymm hsq (sq_nonneg _))
    rcases div_eq_zero_iff.mp this with h | h
    · exact h
    · linarith
  -- `‖g‖² = 0` forces every entry to vanish
  rw [ha, normSq_eq_sum] at ha0
  have hj := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (g[i])).mp ha0 j
    (Finset.mem_univ _)
  rw [← hg]
  exact pow_eq_zero_iff two_ne_zero |>.mp hj

/-- `θ` minimises the least-squares loss iff its gradient vanishes. -/
theorem grad_eq_zero_iff_isMinimizer (θ : Vec ℝ (n + 1)) :
    (∀ j : Fin (n + 1), (mseGrad data θ)[j] = 0) ↔
      ∀ θ' : Vec ℝ (n + 1),
        mse (LinearModel.ofParams θ) data ≤ mse (LinearModel.ofParams θ') data :=
  ⟨fun h _ => mse_le_of_grad_eq_zero data θ h _, grad_eq_zero_of_isMinimizer data θ⟩

end Optimality

/-! ## Normal equations and OLS -/

section NormalEquations

variable {m n : ℕ} (data : Dataset ℝ m n)

/-- `∇L θ = (2/m) (XₐᵀXₐ θ - Xₐᵀ y)`. -/
theorem mseGrad_eq_normal (θ : Vec ℝ (n + 1)) :
    mseGrad data θ = smul (2 / (m : ℝ))
      (vsub (matVec (gram (augmentMat data.X)) θ)
        (matVec (transpose (augmentMat data.X)) data.y)) := by
  rw [matVec_gram, ← matVec_vsub]
  simp [mseGrad, mseGradAux]

/-- The normal equations `XₐᵀXₐ θ = Xₐᵀ y` make the gradient vanish. -/
theorem grad_eq_zero_of_normalEquations (θ : Vec ℝ (n + 1))
    (h : matVec (gram (augmentMat data.X)) θ = matVec (transpose (augmentMat data.X)) data.y)
    (j : Fin (n + 1)) : (mseGrad data θ)[j] = 0 := by
  rw [mseGrad_eq_normal, h]
  simp [smul, vsub]

/-- With at least one sample, a zero gradient means the normal equations hold. -/
theorem normalEquations_of_grad_eq_zero (hm : 0 < m) (θ : Vec ℝ (n + 1))
    (h : ∀ j : Fin (n + 1), (mseGrad data θ)[j] = 0) :
    matVec (gram (augmentMat data.X)) θ = matVec (transpose (augmentMat data.X)) data.y := by
  ext j hj
  have hj' := h ⟨j, hj⟩
  rw [mseGrad_eq_normal] at hj'
  simp only [smul, vsub, Fin.getElem_fin, Vector.getElem_ofFn] at hj'
  have h2m : (2 / m : ℝ) ≠ 0 := div_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hm.ne')
  have := (mul_eq_zero.mp hj').resolve_left h2m
  simpa [sub_eq_zero] using this

/-- The parameters `olsFit` computes. -/
noncomputable abbrev olsParams : Vec ℝ (n + 1) :=
  linSolve (gram (augmentMat data.X)) (matVec (transpose (augmentMat data.X)) data.y)

/-- `linSolve` solved the normal equations. This holds when the augmented features are
linearly independent (`solvesNormalEquations_of_fullColumnRank`). -/
abbrev SolvesNormalEquations : Prop :=
  matVec (gram (augmentMat data.X)) (olsParams data) =
    matVec (transpose (augmentMat data.X)) data.y

/-- **OLS is optimal**: when `linSolve` solved the normal equations, `olsFit` has the
smallest mean squared error of all linear models. -/
theorem olsFit_optimal (hsolve : SolvesNormalEquations data) (model : LinearModel ℝ n) :
    mse (olsFit data) data ≤ mse model data :=
  mse_le_of_grad_eq_zero data (olsParams data)
    (grad_eq_zero_of_normalEquations data _ hsolve) model

/-- If `X` has full column rank, so does its Gram matrix `XᵀX`: `XᵀX θ = 0` gives
`‖X θ‖² = ⟪θ, XᵀX θ⟫ = 0`. -/
theorem fullColumnRank_gram {m k : ℕ} (X : Mat ℝ m k) (hX : FullColumnRank X) :
    FullColumnRank (gram X) := by
  intro θ hθ
  refine hX θ ?_
  have h0 : normSq (matVec X θ) = 0 := by
    rw [normSq, ← dot_matVec_transpose, ← matVec_gram, hθ]
    simp [dot_eq_sum, vzero]
  rw [normSq_eq_sum] at h0
  ext i hi
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).mp h0 ⟨i, hi⟩
    (Finset.mem_univ _)
  simpa [vzero] using pow_eq_zero_iff two_ne_zero |>.mp this

/-- **`linSolve` solves the normal equations** whenever the augmented features are linearly
independent: no feature (or the constant) is a linear combination of the others on the
training data. This is a condition on the data only. -/
theorem solvesNormalEquations_of_fullColumnRank (h : FullColumnRank (augmentMat data.X)) :
    SolvesNormalEquations data :=
  linSolve_spec _ _ (fullColumnRank_gram _ h)

/-- **OLS is optimal on full-rank data**: if the augmented features are linearly
independent, no linear model has a smaller training error than `olsFit`. -/
theorem olsFit_optimal_of_fullColumnRank (h : FullColumnRank (augmentMat data.X))
    (model : LinearModel ℝ n) : mse (olsFit data) data ≤ mse model data :=
  olsFit_optimal data (solvesNormalEquations_of_fullColumnRank data h) model

/-- OLS is never worse than gradient descent, however it is configured. -/
theorem mse_olsFit_le_linRegGD (hsolve : SolvesNormalEquations data) (cfg : GDConfig ℝ) :
    mse (olsFit data) data ≤ mse (linRegGD cfg data) data :=
  olsFit_optimal data hsolve _

theorem mse_olsFit_le_linRegGDSparse (hsolve : SolvesNormalEquations data) (cfg : GDConfig ℝ) :
    mse (olsFit data) data ≤ mse (linRegGDSparse cfg data) data :=
  olsFit_optimal data hsolve _

/-- OLS also fits the targets at least as well as the perceptron's linear model. -/
theorem mse_olsFit_le_perceptronFit (hsolve : SolvesNormalEquations data)
    (cfg : PerceptronConfig ℝ) : mse (olsFit data) data ≤ mse (perceptronFit cfg data) data :=
  olsFit_optimal data hsolve _

end NormalEquations

/-! ## Gradient descent -/

section GradientDescent

variable {m n : ℕ} (data : Dataset ℝ m n)

/-- For `η ≠ 0`, the fixed points of a gradient step are exactly the zeros of the
gradient. -/
theorem gdStep_eq_self_iff {k : ℕ} (obj : Objective ℝ k) {η : ℝ} (hη : η ≠ 0)
    (θ : Vec ℝ k) : gdStep obj η θ = θ ↔ ∀ j : Fin k, (obj.grad θ)[j] = 0 := by
  constructor
  · intro h j
    have hj := congrArg (·[j]) h
    simp only [gdStep_getElem] at hj
    have : η * (obj.grad θ)[j] = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hη
  · intro h
    ext j hj
    simpa [h ⟨j, hj⟩] using gdStep_getElem obj η θ ⟨j, hj⟩

/-- A fixed point of gradient descent (with `η ≠ 0`) is a global least-squares minimiser. -/
theorem mse_le_of_gdStep_eq_self {η : ℝ} (hη : η ≠ 0) (θ : Vec ℝ (n + 1))
    (hfix : gdStep (mseObjective data) η θ = θ) (model : LinearModel ℝ n) :
    mse (LinearModel.ofParams θ) data ≤ mse model data :=
  mse_le_of_grad_eq_zero data θ ((gdStep_eq_self_iff _ hη θ).mp hfix) model

/-- The OLS solution is a fixed point of gradient descent: started there, GD stays. -/
theorem gdStep_olsParams (hsolve : SolvesNormalEquations data) (η : ℝ) :
    gdStep (mseObjective data) η (olsParams data) = olsParams data := by
  ext j hj
  simpa [mseObjective_grad, grad_eq_zero_of_normalEquations data _ hsolve ⟨j, hj⟩] using
    gdStep_getElem (mseObjective data) η (olsParams data) ⟨j, hj⟩

/-- One gradient step changes the loss by exactly
`-η ‖∇L θ‖² + η² (1/m) ∑ᵢ ⟪xᵢ, ∇L θ⟫²`. -/
theorem mse_gdStep (θ : Vec ℝ (n + 1)) (η : ℝ) :
    mse (LinearModel.ofParams (gdStep (mseObjective data) η θ)) data =
      mse (LinearModel.ofParams θ) data - η * normSq (mseGrad data θ) +
        η ^ 2 * (∑ i : Fin m, dot (augment data.X[i]) (mseGrad data θ) ^ 2) / m := by
  have : gdStep (mseObjective data) η θ = vadd θ (smul (-η) (mseGrad data θ)) := by
    ext j hj
    simp only [gdStep, vsub, vadd, smul, Fin.getElem_fin, Vector.getElem_ofFn, mseObjective_grad]
    ring
  rw [this, mse_step, normSq]
  ring

/-- `∑ᵢ ⟪xᵢ, v⟫² ≤ (∑ᵢ ‖xᵢ‖²) ‖v‖²` (Cauchy–Schwarz on every row). -/
theorem sum_dot_sq_le (v : Vec ℝ (n + 1)) :
    ∑ i : Fin m, dot (augment data.X[i]) v ^ 2 ≤
      (∑ i : Fin m, normSq (augment data.X[i])) * normSq v := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => dot_sq_le _ _

/-- **Descent**: with `0 ≤ η` and `η ∑ᵢ ‖xᵢ‖² ≤ m`, a gradient step never increases the
loss. (`∑ᵢ ‖xᵢ‖²` bounds `m L/2`, where `L` is the smoothness constant, so this is the
classical `η ≤ 1/L` condition, made checkable.) -/
theorem mse_gdStep_le (θ : Vec ℝ (n + 1)) {η : ℝ} (hη : 0 ≤ η)
    (hstep : η * ∑ i : Fin m, normSq (augment data.X[i]) ≤ m) :
    mse (LinearModel.ofParams (gdStep (mseObjective data) η θ)) data ≤
      mse (LinearModel.ofParams θ) data := by
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
        η * normSq (mseGrad data θ) := by
      rw [div_le_iff₀ hm']
      nlinarith [h1, h2]
    linarith

/-- Under the same step-size condition, each iteration of `linRegGD` is at least as good
as the previous one. -/
theorem mse_linRegGD_succ_le {η : ℝ} (hη : 0 ≤ η)
    (hstep : η * ∑ i : Fin m, normSq (augment data.X[i]) ≤ m) (k : ℕ) :
    mse (linRegGD ⟨η, k + 1⟩ data) data ≤ mse (linRegGD ⟨η, k⟩ data) data := by
  simp only [linRegGD]
  rw [gradientDescent_succ]
  exact mse_gdStep_le data _ hη hstep

/-- The training loss of `linRegGD` is non-increasing in the number of iterations. -/
theorem mse_linRegGD_antitone {η : ℝ} (hη : 0 ≤ η)
    (hstep : η * ∑ i : Fin m, normSq (augment data.X[i]) ≤ m) :
    Antitone fun k => mse (linRegGD ⟨η, k⟩ data) data :=
  antitone_nat_of_succ_le (mse_linRegGD_succ_le data hη hstep)

/-- The same for the sparse solver, which runs the same iterates. -/
theorem mse_linRegGDSparse_antitone {η : ℝ} (hη : 0 ≤ η)
    (hstep : η * ∑ i : Fin m, normSq (augment data.X[i]) ≤ m) :
    Antitone fun k => mse (linRegGDSparse ⟨η, k⟩ data) data := by
  simpa only [linRegGDSparse_eq] using mse_linRegGD_antitone data hη hstep

end GradientDescent

end ML

end
