/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
import LeanLearn.Regression.Solvers
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# LeanLearn.Proofs.Regression.Basic

Linear regression — the loss is an exact quadratic.

Over `ℝ`, for a problem `P` with normal equations `A θ = b` (`A = P.normalMatrix`,
`b = P.normalVector`) and ridge penalty `λ`:

* **Entries** (`normalMatrix_apply`, `normalVector_apply`, `residual_apply`): the executable
  folds are the textbook sums.
* **Exact expansion** (`loss_add`): `L(θ + v) = L(θ) + 2 ⟪A θ - b, v⟫ + C(v)`, where the
  *curvature* `C(v) = (1/m) ∑ᵣ ⟪xᵣ, v⟫² + λ ‖v‖²` is `vᵀ A v` (`curvature_eq`) and is
  non-negative for `λ ≥ 0`. So the loss is convex and `A θ - b` is half its gradient.
* **Optimality** (`loss_le_of_residual_eq_zero`): a solution of the normal equations
  minimises the loss over all parameters, and `L(u) - L(θ*) = C(u - θ*)` exactly.
* **Smoothness** (`curvature_le`): `C(v) ≤ Λ ‖v‖²` with `Λ = (1/m) ∑ᵣ ‖xᵣ‖² + λ`.
* **Degenerate coordinates** (`residual_eq_zero_of_diag_eq_zero`): if `Aᵢᵢ = 0` then the
  `i`-th equation is `0 = 0`, so Jacobi and Gauss–Seidel lose nothing by dividing by zero.
-/

namespace LeanLearn.Regression

open Finset

/-! ## Sums -/

section Sums

variable {n : ℕ}

theorem sumFin_eq_sum (f : Fin n → ℝ) : sumFin f = ∑ i, f i := by
  rw [sumFin, sumGen_eq, Fin.sum_univ_def]

@[simp] theorem count_real (k : ℕ) : (count k : ℝ) = k := by
  rw [count, nsmulGen_eq, mul_one]

theorem dot_eq_sum (u v : Vec ℝ n) : dot u v = ∑ i : Fin n, u[i] * v[i] := sumFin_eq_sum _

theorem dot_self_nonneg (v : Vec ℝ n) : 0 ≤ dot v v := by
  rw [dot_eq_sum]
  exact sum_nonneg fun i _ ↦ mul_self_nonneg _

@[simp] theorem vadd_getElem (u v : Vec ℝ n) (i : Fin n) : (vadd u v)[i] = u[i] + v[i] := by
  simp [vadd]

@[simp] theorem vsub_getElem (u v : Vec ℝ n) (i : Fin n) : (vsub u v)[i] = u[i] - v[i] := by
  simp [vsub]

@[simp] theorem smul_getElem (c : ℝ) (v : Vec ℝ n) (i : Fin n) : (smul c v)[i] = c * v[i] := by
  simp [smul]

@[simp] theorem vzero_getElem (i : Fin n) : (vzero : Vec ℝ n)[i] = 0 := by
  simp [vzero]

/-! The same with natural-number indices, the form `simp` normalises to. -/

@[simp] theorem vadd_getElem' (u v : Vec ℝ n) (i : ℕ) (h : i < n) :
    (vadd u v)[i] = u[i] + v[i] := by simp [vadd]

@[simp] theorem vsub_getElem' (u v : Vec ℝ n) (i : ℕ) (h : i < n) :
    (vsub u v)[i] = u[i] - v[i] := by simp [vsub]

@[simp] theorem smul_getElem' (c : ℝ) (v : Vec ℝ n) (i : ℕ) (h : i < n) :
    (smul c v)[i] = c * v[i] := by simp [smul]

@[simp] theorem vzero_getElem' (i : ℕ) (h : i < n) : (vzero : Vec ℝ n)[i] = 0 := by
  simp [vzero]

theorem matVec_getElem {m : ℕ} (A : Mat ℝ m n) (v : Vec ℝ n) (i : Fin m) :
    (matVec A v)[i] = ∑ j : Fin n, A[i][j] * v[j] := by
  simp [matVec, dot_eq_sum]

theorem dot_vadd (u v w : Vec ℝ n) : dot u (vadd v w) = dot u v + dot u w := by
  simp only [dot_eq_sum, vadd_getElem, mul_add, sum_add_distrib]

theorem dot_smul (u v : Vec ℝ n) (c : ℝ) : dot u (smul c v) = c * dot u v := by
  simp only [dot_eq_sum, smul_getElem, mul_sum]
  exact sum_congr rfl fun i _ ↦ by ring

theorem vext {u v : Vec ℝ n} (h : ∀ i : Fin n, u[i] = v[i]) : u = v := by
  ext i hi
  exact h ⟨i, hi⟩

end Sums

/-! ## The problem's entries -/

namespace Problem

variable {m d : ℕ} (P : Problem ℝ m d)

/-- Entry `i` of sample `r` with the constant `1` appended. -/
noncomputable abbrev x (r : Fin m) (i : Fin (d + 1)) : ℝ := (P.row r)[i]

/-- The fitted value `⟪xᵣ, θ⟫`. -/
noncomputable abbrev fit (r : Fin m) (θ : Vec ℝ (d + 1)) : ℝ := dot (P.row r) θ

theorem fit_eq (r : Fin m) (θ : Vec ℝ (d + 1)) : P.fit r θ = ∑ i, P.x r i * θ[i] :=
  dot_eq_sum _ _

@[simp] theorem design_getElem (r : Fin m) : P.design[r] = P.row r := by
  simp [design]

theorem normalMatrix_apply (i j : Fin (d + 1)) :
    P.normalMatrix[i][j] = (∑ r, P.x r i * P.x r j) / m + if i = j then P.ridge else 0 := by
  simp [normalMatrix, design, sumFin_eq_sum]

theorem normalVector_apply (i : Fin (d + 1)) :
    P.normalVector[i] = (∑ r, P.x r i * P.y[r]) / m := by
  simp [normalVector, design, sumFin_eq_sum]

theorem normalMatrix_symm (i j : Fin (d + 1)) : P.normalMatrix[i][j] = P.normalMatrix[j][i] := by
  rw [normalMatrix_apply, normalMatrix_apply]
  congr 1
  · exact congrArg (· / (m : ℝ)) (sum_congr rfl fun r _ ↦ mul_comm _ _)
  · by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]

theorem loss_eq (θ : Vec ℝ (d + 1)) :
    P.loss θ = (∑ r, (P.fit r θ - P.y[r]) ^ 2) / m + P.ridge * ∑ i : Fin (d + 1), θ[i] ^ 2 := by
  simp only [loss, sumFin_eq_sum, count_real, sq]
  rw [dot_eq_sum]

/-- `∑ⱼ (∑ᵣ xᵣᵢ xᵣⱼ) θⱼ = ∑ᵣ xᵣᵢ ⟪xᵣ, θ⟫`. -/
theorem sum_gram_mul (i : Fin (d + 1)) (θ : Vec ℝ (d + 1)) :
    ∑ j : Fin (d + 1), (∑ r, P.x r i * P.x r j) * θ[j] = ∑ r, P.x r i * P.fit r θ := by
  simp only [fit_eq, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun r _ ↦ sum_congr rfl fun j _ ↦ by ring

/-- The residual of the normal equations, `(A θ - b)ᵢ`. -/
theorem residual_apply (θ : Vec ℝ (d + 1)) (i : Fin (d + 1)) :
    (residual P.normalMatrix P.normalVector θ)[i] =
      (∑ r, P.x r i * (P.fit r θ - P.y[r])) / m + P.ridge * θ[i] := by
  rw [residual, vsub_getElem, matVec_getElem, normalVector_apply]
  have hA : ∀ j : Fin (d + 1), P.normalMatrix[i][j] * θ[j] =
      (∑ r, P.x r i * P.x r j) * θ[j] / m + if i = j then P.ridge * θ[j] else 0 := fun j ↦ by
    rw [normalMatrix_apply]
    split_ifs <;> ring
  rw [sum_congr rfl fun j _ ↦ hA j, sum_add_distrib, sum_ite_eq, if_pos (mem_univ _),
    ← sum_div, sum_gram_mul]
  simp only [mul_sub, sum_sub_distrib]
  ring

/-- The curvature `C(v) = (1/m) ∑ᵣ ⟪xᵣ, v⟫² + λ ‖v‖²`: the second-order part of the
loss. -/
noncomputable def curvature (v : Vec ℝ (d + 1)) : ℝ :=
  (∑ r, P.fit r v ^ 2) / m + P.ridge * ∑ i : Fin (d + 1), v[i] ^ 2

theorem curvature_nonneg (hridge : 0 ≤ P.ridge) (v : Vec ℝ (d + 1)) : 0 ≤ P.curvature v :=
  add_nonneg (div_nonneg (sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg m))
    (mul_nonneg hridge (sum_nonneg fun _ _ ↦ sq_nonneg _))

theorem curvature_smul (c : ℝ) (v : Vec ℝ (d + 1)) :
    P.curvature (smul c v) = c ^ 2 * P.curvature v := by
  simp only [curvature, dot_smul, smul_getElem, mul_pow, ← mul_sum]
  ring

/-- `∑ᵢ (A θ - b)ᵢ vᵢ = (1/m) ∑ᵣ (⟪xᵣ, θ⟫ - yᵣ) ⟪xᵣ, v⟫ + λ ⟪θ, v⟫`. -/
theorem sum_residual_mul (θ v : Vec ℝ (d + 1)) :
    ∑ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] * v[i] =
      (∑ r, (P.fit r θ - P.y[r]) * P.fit r v) / m +
        P.ridge * ∑ i : Fin (d + 1), θ[i] * v[i] := by
  have h : ∀ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] * v[i] =
      (∑ r, P.x r i * (P.fit r θ - P.y[r])) * v[i] / m + P.ridge * (θ[i] * v[i]) := fun i ↦ by
    rw [residual_apply]; ring
  rw [sum_congr rfl fun i _ ↦ h i, sum_add_distrib, ← sum_div, ← mul_sum]
  congr 2
  simp only [fit_eq, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun r _ ↦ sum_congr rfl fun i _ ↦ by ring

/-- **The loss is an exact quadratic**: `L(θ + v) = L(θ) + 2 ⟪A θ - b, v⟫ + C(v)`. -/
theorem loss_add (θ v : Vec ℝ (d + 1)) :
    P.loss (vadd θ v) = P.loss θ +
      2 * ∑ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] * v[i] +
        P.curvature v := by
  rw [sum_residual_mul, loss_eq, loss_eq, curvature]
  simp only [fit, dot_vadd, vadd_getElem]
  have h1 : ∀ r : Fin m, (dot (P.row r) θ + dot (P.row r) v - P.y[r]) ^ 2 =
      (dot (P.row r) θ - P.y[r]) ^ 2 + 2 * ((dot (P.row r) θ - P.y[r]) * dot (P.row r) v) +
        dot (P.row r) v ^ 2 := fun r ↦ by ring
  have h2 : ∀ i : Fin (d + 1), (θ[i] + v[i]) ^ 2 = θ[i] ^ 2 + 2 * (θ[i] * v[i]) + v[i] ^ 2 :=
    fun i ↦ by ring
  simp only [h1, h2, sum_add_distrib, ← mul_sum]
  ring

/-- **Convexity**: the loss lies above its tangent planes. -/
theorem loss_ge_tangent (hridge : 0 ≤ P.ridge) (θ u : Vec ℝ (d + 1)) :
    P.loss θ + 2 * ∑ i : Fin (d + 1),
      (residual P.normalMatrix P.normalVector θ)[i] * (u[i] - θ[i]) ≤ P.loss u := by
  have h := P.loss_add θ (vsub u θ)
  have hu : vadd θ (vsub u θ) = u := vext fun i ↦ by simp [vadd, vsub]
  rw [hu] at h
  simp only [vsub_getElem] at h
  linarith [P.curvature_nonneg hridge (vsub u θ)]

/-- **Optimality**: a solution of the normal equations minimises the loss, and the
excess loss of any `u` is exactly `C(u - θ*)`. -/
theorem loss_eq_of_residual_eq_zero {θ : Vec ℝ (d + 1)}
    (h : ∀ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] = 0)
    (u : Vec ℝ (d + 1)) : P.loss u = P.loss θ + P.curvature (vsub u θ) := by
  have h' := P.loss_add θ (vsub u θ)
  have hu : vadd θ (vsub u θ) = u := vext fun i ↦ by simp [vadd, vsub]
  rw [hu] at h'
  simp only [h, zero_mul, sum_const_zero, mul_zero, add_zero] at h'
  exact h'

theorem loss_le_of_residual_eq_zero (hridge : 0 ≤ P.ridge) {θ : Vec ℝ (d + 1)}
    (h : ∀ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] = 0)
    (u : Vec ℝ (d + 1)) : P.loss θ ≤ P.loss u := by
  rw [P.loss_eq_of_residual_eq_zero h u]
  linarith [P.curvature_nonneg hridge (vsub u θ)]

/-- The curvature is the quadratic form of `A`: `C(v) = vᵀ A v`. -/
theorem curvature_eq (v : Vec ℝ (d + 1)) :
    P.curvature v =
      ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), P.normalMatrix[i][j] * v[i] * v[j] := by
  simp only [normalMatrix_apply, add_mul, sum_add_distrib, curvature, fit_eq]
  congr 1
  · simp only [div_mul_eq_mul_div, ← sum_div, sq, sum_mul, mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun r _ ↦ ?_
    rw [sum_comm]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  · simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true, mul_sum, sq]
    exact sum_congr rfl fun i _ ↦ by ring

/-- **Smoothness**: `C(v) ≤ Λ ‖v‖²` with `Λ = (1/m) ∑ᵣ ‖xᵣ‖² + λ` (Cauchy–Schwarz on every
sample). -/
theorem curvature_le (v : Vec ℝ (d + 1)) :
    P.curvature v ≤
      ((∑ r, ∑ i, P.x r i ^ 2) / m + P.ridge) * ∑ i : Fin (d + 1), v[i] ^ 2 := by
  rw [curvature, add_mul, div_mul_eq_mul_div, sum_mul]
  gcongr with r _
  rw [fit_eq]
  exact sum_mul_sq_le_sq_mul_sq _ _ _

/-- If the diagonal entry `Aᵢᵢ` vanishes (with `λ ≥ 0`), the `i`-th residual vanishes:
feature `i` is zero on every sample and unpenalised, so equation `i` reads `0 = 0`. -/
theorem residual_eq_zero_of_diag_eq_zero (hridge : 0 ≤ P.ridge) {i : Fin (d + 1)}
    (hA : P.normalMatrix[i][i] = 0) (θ : Vec ℝ (d + 1)) :
    (residual P.normalMatrix P.normalVector θ)[i] = 0 := by
  rw [normalMatrix_apply, if_pos rfl] at hA
  have hs : 0 ≤ (∑ r, P.x r i * P.x r i) / m :=
    div_nonneg (sum_nonneg fun _ _ ↦ mul_self_nonneg _) (Nat.cast_nonneg m)
  have hridge0 : P.ridge = 0 := by linarith
  have hsum : (∑ r, P.x r i * P.x r i) / m = 0 := by linarith
  rw [residual_apply, hridge0, zero_mul, add_zero]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    rw [div_eq_zero_iff, or_iff_left hm'] at hsum
    have hx : ∀ r, P.x r i = 0 := fun r ↦
      mul_self_eq_zero.mp ((sum_eq_zero_iff_of_nonneg fun _ _ ↦ mul_self_nonneg _).mp hsum r
        (mem_univ r))
    simp [hx]

/-- If `Aᵢᵢ = 0`, the curvature does not see coordinate `i`. -/
theorem normalMatrix_row_eq_zero (hridge : 0 ≤ P.ridge) {i : Fin (d + 1)}
    (hA : P.normalMatrix[i][i] = 0) (j : Fin (d + 1)) : P.normalMatrix[i][j] = 0 := by
  rw [normalMatrix_apply, if_pos rfl] at hA
  have hs : 0 ≤ (∑ r, P.x r i * P.x r i) / m :=
    div_nonneg (sum_nonneg fun _ _ ↦ mul_self_nonneg _) (Nat.cast_nonneg m)
  have hridge0 : P.ridge = 0 := by linarith
  have hsum : (∑ r, P.x r i * P.x r i) / m = 0 := by linarith
  rw [normalMatrix_apply, hridge0]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    rw [div_eq_zero_iff, or_iff_left hm'] at hsum
    have hx : ∀ r, P.x r i = 0 := fun r ↦
      mul_self_eq_zero.mp ((sum_eq_zero_iff_of_nonneg fun _ _ ↦ mul_self_nonneg _).mp hsum r
        (mem_univ r))
    simp [hx]

end Problem

end LeanLearn.Regression
