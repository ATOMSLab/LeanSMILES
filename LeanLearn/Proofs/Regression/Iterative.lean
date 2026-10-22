/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
-/
module

public import LeanLearn.Proofs.Regression.Basic
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# LeanLearn.Proofs.Regression.Iterative

Jacobi and Gauss–Seidel iteration.

**Weighted diagonal dominance** (`DiagDominant A w ρ`): weights `wᵢ > 0`, a ratio
`0 ≤ ρ < 1`, positive diagonal, and for every row `∑_{j≠i} |Aᵢⱼ| wⱼ ≤ ρ Aᵢᵢ wᵢ`. With
`w = 1` this is strict diagonal dominance; other weights certify more matrices.

For any linear system `A θ = b` (`A` need not come from regression):

* **A solution exists** (`exists_solution`), by Gershgorin's theorem applied to `A`
  scaled by the weights.
* **Both iterations contract** (`jacobiStep_bound`, `gsSweep_bound`): if every
  `|θⱼ - θ*ⱼ| ≤ M wⱼ` before a Jacobi step or a Gauss–Seidel sweep, then every
  `|θⱼ - θ*ⱼ| ≤ ρ M wⱼ` after it. So after `k` steps from `θ = 0`,
  `|θₖ,ⱼ - θ*ⱼ| ≤ ρᵏ β wⱼ` (`jacobi_bound`, `gaussSeidel_bound`), where
  `|θ*ⱼ| ≤ β wⱼ` follows from `|bᵢ| ≤ (1 - ρ) Aᵢᵢ wᵢ β` (`solution_bound`).

For the normal equations of a ridge problem (`λ ≥ 0`):

* **Excess loss** (`loss_jacobi_le`, `loss_gaussSeidel_le`): after `k` steps,
  `L(θₖ) ≤ L(u) + Γ β² ρ²ᵏ` for every `u`, with `Γ = ∑ᵢⱼ |Aᵢⱼ| wᵢ wⱼ`.
* **Gauss–Seidel never increases the loss** (`loss_gaussSeidel_antitone`), with no
  condition at all: each coordinate update minimises the loss exactly along that
  coordinate (it is coordinate descent).
* **Fixed points are optimal** (`loss_le_of_jacobiStep_eq_self`): a fixed point of Jacobi
  solves the normal equations, so it minimises the loss.
-/

@[expose] public section

namespace LeanLearn.Regression

open Finset

variable {n : ℕ}

/-! ## Off-diagonal sums -/

/-- `∑_{j≠i} |Aᵢⱼ| wⱼ`. -/
noncomputable def offDiagWeight (A : Mat ℝ n n) (w : Vec ℝ n) (i : Fin n) : ℝ :=
  ∑ j : Fin n, if j = i then 0 else |A[i][j]| * w[j]

/-- `Γ = ∑ᵢⱼ |Aᵢⱼ| wᵢ wⱼ`. -/
noncomputable def weightedMass (A : Mat ℝ n n) (w : Vec ℝ n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, |A[i][j]| * w[i] * w[j]

/-- **Weighted diagonal dominance** with weights `w` and ratio `ρ`. -/
structure DiagDominant (A : Mat ℝ n n) (w : Vec ℝ n) (ρ : ℝ) : Prop where
  ratio_nonneg : 0 ≤ ρ
  ratio_lt_one : ρ < 1
  weight_pos : ∀ i : Fin n, 0 < w[i]
  diag_pos : ∀ i : Fin n, 0 < A[i][i]
  dominant : ∀ i : Fin n, offDiagWeight A w i ≤ ρ * A[i][i] * w[i]

theorem dot_getElem_eq (A : Mat ℝ n n) (θ : Vec ℝ n) (i : Fin n) :
    dot A[i] θ = ∑ j : Fin n, A[i][j] * θ[j] := dot_eq_sum _ _

theorem offDiag_eq_sum (A : Mat ℝ n n) (θ : Vec ℝ n) (i : Fin n) :
    offDiag A θ i = ∑ j : Fin n, if j = i then 0 else A[i][j] * θ[j] := by
  rw [offDiag, dot_getElem_eq]
  have h : ∀ j : Fin n, A[i][j] * θ[j] =
      (if j = i then A[i][j] * θ[j] else 0) + if j = i then 0 else A[i][j] * θ[j] :=
    fun j ↦ by split_ifs <;> simp
  rw [sum_congr rfl fun j _ ↦ h j, sum_add_distrib, sum_ite_eq']
  simp

theorem offDiag_sub (A : Mat ℝ n n) (θ θ' : Vec ℝ n) (i : Fin n) :
    offDiag A θ i - offDiag A θ' i = offDiag A (vsub θ θ') i := by
  simp only [offDiag_eq_sum, ← sum_sub_distrib, vsub_getElem]
  exact sum_congr rfl fun j _ ↦ by split_ifs <;> ring

theorem abs_offDiag_le (A : Mat ℝ n n) (w e : Vec ℝ n) {M : ℝ}
    (he : ∀ j : Fin n, |e[j]| ≤ M * w[j]) (i : Fin n) :
    |offDiag A e i| ≤ M * offDiagWeight A w i := by
  rw [offDiag_eq_sum, offDiagWeight, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
  split_ifs
  · simp
  · rw [abs_mul]
    calc |A[i][j]| * |e[j]| ≤ |A[i][j]| * (M * w[j]) :=
          mul_le_mul_of_nonneg_left (he j) (abs_nonneg _)
      _ = M * (|A[i][j]| * w[j]) := by ring

/-! ## One coordinate update -/

theorem coordSolve_of_ne {A : Mat ℝ n n} {b θ : Vec ℝ n} {i : Fin n} (hA : A[i][i] ≠ 0) :
    coordSolve A b θ i = (b[i] - offDiag A θ i) / A[i][i] := by
  rw [coordSolve, if_neg (by simpa using hA)]

theorem coordSolve_of_eq {A : Mat ℝ n n} {b θ : Vec ℝ n} {i : Fin n} (hA : A[i][i] = 0) :
    coordSolve A b θ i = θ[i] := by
  rw [coordSolve, if_pos (by simpa using hA)]

section Update

variable {A : Mat ℝ n n} {b θs : Vec ℝ n}

/-- A solution satisfies `bᵢ = ∑_{j≠i} Aᵢⱼ θ*ⱼ + Aᵢᵢ θ*ᵢ`. -/
theorem solution_row (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) (i : Fin n) :
    b[i] = offDiag A θs i + A[i][i] * θs[i] := by
  rw [← hsol i, offDiag]
  simp [matVec]

/-- The new value of coordinate `i` (Jacobi or Gauss–Seidel), minus the solution:
`-(∑_{j≠i} Aᵢⱼ (θⱼ - θ*ⱼ)) / Aᵢᵢ`. -/
theorem update_sub (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) (θ : Vec ℝ n) (i : Fin n)
    (hA : A[i][i] ≠ 0) :
    (b[i] - offDiag A θ i) / A[i][i] - θs[i] = -offDiag A (vsub θ θs) i / A[i][i] := by
  rw [solution_row hsol i, ← offDiag_sub]
  field_simp
  ring

/-- **One coordinate update contracts**: if every `|θⱼ - θ*ⱼ| ≤ M wⱼ`, the updated
coordinate has `|θᵢ' - θ*ᵢ| ≤ ρ M wᵢ`. -/
theorem update_bound {w : Vec ℝ n} {ρ : ℝ} (hdd : DiagDominant A w ρ)
    (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) {M : ℝ} (hM : 0 ≤ M) (θ : Vec ℝ n)
    (hθ : ∀ j : Fin n, |θ[j] - θs[j]| ≤ M * w[j]) (i : Fin n) :
    |(b[i] - offDiag A θ i) / A[i][i] - θs[i]| ≤ ρ * M * w[i] := by
  have hAi := hdd.diag_pos i
  rw [update_sub hsol θ i hAi.ne', abs_div, abs_neg, abs_of_pos hAi, div_le_iff₀ hAi]
  have he : ∀ j : Fin n, |(vsub θ θs)[j]| ≤ M * w[j] := fun j ↦ by simpa using hθ j
  calc |offDiag A (vsub θ θs) i| ≤ M * offDiagWeight A w i := abs_offDiag_le A w _ he i
    _ ≤ M * (ρ * A[i][i] * w[i]) := mul_le_mul_of_nonneg_left (hdd.dominant i) hM
    _ = ρ * M * w[i] * A[i][i] := by ring

end Update

/-! ## Jacobi -/

section Jacobi

variable {A : Mat ℝ n n} {b θs w : Vec ℝ n} {ρ : ℝ}

@[simp] theorem jacobiStep_getElem (θ : Vec ℝ n) (i : Fin n) :
    (jacobiStep A b θ)[i] = coordSolve A b θ i := by
  simp [jacobiStep]

/-- **A Jacobi step contracts** by `ρ` in the weighted norm. -/
theorem jacobiStep_bound (hdd : DiagDominant A w ρ) (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i])
    {M : ℝ} (hM : 0 ≤ M) (θ : Vec ℝ n) (hθ : ∀ j : Fin n, |θ[j] - θs[j]| ≤ M * w[j])
    (i : Fin n) : |(jacobiStep A b θ)[i] - θs[i]| ≤ ρ * M * w[i] := by
  rw [jacobiStep_getElem, coordSolve_of_ne (hdd.diag_pos i).ne']
  exact update_bound hdd hsol hM θ hθ i

/-- After `k` Jacobi steps, `|θₖ,ⱼ - θ*ⱼ| ≤ ρᵏ M wⱼ`. -/
theorem jacobi_iterate_bound (hdd : DiagDominant A w ρ)
    (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) {M : ℝ} (hM : 0 ≤ M) (θ₀ : Vec ℝ n)
    (h₀ : ∀ j : Fin n, |θ₀[j] - θs[j]| ≤ M * w[j]) (k : ℕ) (i : Fin n) :
    |((jacobiStep A b)^[k] θ₀)[i] - θs[i]| ≤ ρ ^ k * M * w[i] := by
  induction k generalizing i with
  | zero => simpa using h₀ i
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := jacobiStep_bound hdd hsol (mul_nonneg (pow_nonneg hdd.ratio_nonneg k) hM) _ ih i
    calc _ ≤ ρ * (ρ ^ k * M) * w[i] := this
      _ = ρ ^ (k + 1) * M * w[i] := by ring

end Jacobi

/-! ## Gauss–Seidel -/

section GaussSeidel

variable {A : Mat ℝ n n} {b θs w : Vec ℝ n} {ρ : ℝ}

theorem gsUpdate_getElem (θ : Vec ℝ n) (i j : Fin n) :
    (gsUpdate A b θ i)[j] = if j = i then coordSolve A b θ i else θ[j] := by
  simp only [gsUpdate, Fin.getElem_fin, Vector.getElem_set]
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg (fun h' ↦ h (Fin.ext h'.symm)), if_neg h]

/-- The Gauss–Seidel invariant over a list of coordinates: every coordinate stays within
`M wⱼ`, and every coordinate updated so far is within `ρ M wⱼ`. -/
theorem foldl_gsUpdate_bound (hdd : DiagDominant A w ρ)
    (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) {M : ℝ} (hM : 0 ≤ M) (l : List (Fin n))
    (θ : Vec ℝ n) (done : Fin n → Prop) (hθ : ∀ j : Fin n, |θ[j] - θs[j]| ≤ M * w[j])
    (hdone : ∀ j, done j → |θ[j] - θs[j]| ≤ ρ * M * w[j]) :
    (∀ j : Fin n, |(l.foldl (gsUpdate A b) θ)[j] - θs[j]| ≤ M * w[j]) ∧
      ∀ j, (done j ∨ j ∈ l) → |(l.foldl (gsUpdate A b) θ)[j] - θs[j]| ≤ ρ * M * w[j] := by
  induction l generalizing θ done with
  | nil => exact ⟨hθ, fun j hj ↦ hdone j (hj.resolve_right (List.not_mem_nil))⟩
  | cons i l ih =>
    simp only [List.foldl_cons]
    have hnew := update_bound hdd hsol hM θ hθ i
    rw [← coordSolve_of_ne (hdd.diag_pos i).ne'] at hnew
    have hρM : ρ * M * w[i] ≤ M * w[i] := by
      have := hdd.weight_pos i
      have : ρ * M ≤ M := by nlinarith [hdd.ratio_lt_one]
      nlinarith
    have hθ' : ∀ j : Fin n, |(gsUpdate A b θ i)[j] - θs[j]| ≤ M * w[j] := fun j ↦ by
      rw [gsUpdate_getElem]
      split_ifs with h
      · subst h; exact hnew.trans hρM
      · exact hθ j
    have hdone' : ∀ j, (done j ∨ j = i) →
        |(gsUpdate A b θ i)[j] - θs[j]| ≤ ρ * M * w[j] := fun j hj ↦ by
      rw [gsUpdate_getElem]
      split_ifs with h
      · subst h; exact hnew
      · exact hdone j (hj.resolve_right h)
    obtain ⟨h1, h2⟩ := ih (gsUpdate A b θ i) (fun j ↦ done j ∨ j = i) hθ' hdone'
    refine ⟨h1, fun j hj ↦ h2 j ?_⟩
    rcases hj with hj | hj
    · exact Or.inl (Or.inl hj)
    · rcases List.mem_cons.mp hj with rfl | hj
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr hj

/-- **A Gauss–Seidel sweep contracts** by `ρ` in the weighted norm. -/
theorem gsSweep_bound (hdd : DiagDominant A w ρ) (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i])
    {M : ℝ} (hM : 0 ≤ M) (θ : Vec ℝ n) (hθ : ∀ j : Fin n, |θ[j] - θs[j]| ≤ M * w[j])
    (i : Fin n) : |(gsSweep A b θ)[i] - θs[i]| ≤ ρ * M * w[i] :=
  (foldl_gsUpdate_bound hdd hsol hM _ θ (fun _ ↦ False) hθ (fun _ h ↦ h.elim)).2 i
    (Or.inr (List.mem_finRange i))

/-- After `k` Gauss–Seidel sweeps, `|θₖ,ⱼ - θ*ⱼ| ≤ ρᵏ M wⱼ`. -/
theorem gaussSeidel_iterate_bound (hdd : DiagDominant A w ρ)
    (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) {M : ℝ} (hM : 0 ≤ M) (θ₀ : Vec ℝ n)
    (h₀ : ∀ j : Fin n, |θ₀[j] - θs[j]| ≤ M * w[j]) (k : ℕ) (i : Fin n) :
    |((gsSweep A b)^[k] θ₀)[i] - θs[i]| ≤ ρ ^ k * M * w[i] := by
  induction k generalizing i with
  | zero => simpa using h₀ i
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := gsSweep_bound hdd hsol (mul_nonneg (pow_nonneg hdd.ratio_nonneg k) hM) _ ih i
    calc _ ≤ ρ * (ρ ^ k * M) * w[i] := this
      _ = ρ ^ (k + 1) * M * w[i] := by ring

end GaussSeidel

/-! ## The solution: existence and size -/

section Solution

variable {A : Mat ℝ n n} {b w : Vec ℝ n} {ρ : ℝ}

/-- The matrix as Mathlib sees it. -/
noncomputable def toMatrix (A : Mat ℝ n n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦ A[i][j]

theorem det_ne_zero (hdd : DiagDominant A w ρ) : (toMatrix A).det ≠ 0 := by
  -- scale column `j` by `wⱼ`: the result is strictly diagonally dominant
  set D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal fun j ↦ w[j]
  have hB : (toMatrix A * D).det ≠ 0 := by
    refine det_ne_zero_of_sum_row_lt_diag fun i ↦ ?_
    have hentry : ∀ j, (toMatrix A * D) i j = A[i][j] * w[j] := fun j ↦ by
      simp [D, toMatrix, Matrix.mul_diagonal]
    simp only [hentry, Real.norm_eq_abs, abs_mul, abs_of_pos (hdd.weight_pos _)]
    have hsum : ∑ j ∈ univ.erase i, |A[i][j]| * w[j] = offDiagWeight A w i := by
      rw [offDiagWeight, ← sum_erase_add _ _ (mem_univ i), if_pos rfl, add_zero]
      exact sum_congr rfl fun j hj ↦ by rw [if_neg (ne_of_mem_erase hj)]
    rw [hsum, abs_of_pos (hdd.diag_pos i)]
    have hpos : 0 < A[i][i] * w[i] := mul_pos (hdd.diag_pos i) (hdd.weight_pos i)
    calc offDiagWeight A w i ≤ ρ * A[i][i] * w[i] := hdd.dominant i
      _ = ρ * (A[i][i] * w[i]) := by ring
      _ < 1 * (A[i][i] * w[i]) := mul_lt_mul_of_pos_right hdd.ratio_lt_one hpos
      _ = A[i][i] * w[i] := one_mul _
  rw [Matrix.det_mul] at hB
  exact left_ne_zero_of_mul hB

/-- **A solution exists** when `A` is weighted diagonally dominant. -/
theorem exists_solution (hdd : DiagDominant A w ρ) (b : Vec ℝ n) :
    ∃ θs : Vec ℝ n, ∀ i : Fin n, (matVec A θs)[i] = b[i] := by
  have hu : IsUnit (toMatrix A).det := isUnit_iff_ne_zero.mpr (det_ne_zero hdd)
  let v : Fin n → ℝ := (toMatrix A)⁻¹.mulVec fun j ↦ b[j]
  refine ⟨Vector.ofFn v, fun i ↦ ?_⟩
  have h : (toMatrix A).mulVec v = fun j ↦ b[j] := by
    simp only [v, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have := congrFun h i
  rw [matVec_getElem]
  simpa [toMatrix, Matrix.mulVec, dotProduct] using this

/-- **The size of the solution**: if `|bᵢ| ≤ (1 - ρ) Aᵢᵢ wᵢ β` for every row, then
`|θ*ᵢ| ≤ β wᵢ`. -/
theorem solution_bound (hdd : DiagDominant A w ρ) {θs : Vec ℝ n}
    (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) {β : ℝ}
    (hb : ∀ i : Fin n, |b[i]| ≤ (1 - ρ) * A[i][i] * w[i] * β) (i : Fin n) :
    |θs[i]| ≤ β * w[i] := by
  -- the coordinate where `|θ*ⱼ| / wⱼ` is largest
  obtain ⟨i₀, -, hmax⟩ := exists_max_image univ (fun j : Fin n ↦ |θs[j]| / w[j])
    ⟨i, mem_univ i⟩
  set M := |θs[i₀]| / w[i₀]
  have hw₀ := hdd.weight_pos i₀
  have hall : ∀ j : Fin n, |θs[j]| ≤ M * w[j] := fun j ↦ by
    have := hmax j (mem_univ j)
    rwa [div_le_iff₀ (hdd.weight_pos j)] at this
  have hM : 0 ≤ M := div_nonneg (abs_nonneg _) hw₀.le
  -- row `i₀`: `Aᵢᵢ |θ*ᵢ| ≤ |bᵢ| + ρ Aᵢᵢ wᵢ M`
  have hrow := solution_row hsol i₀
  have hA := hdd.diag_pos i₀
  have hoff : |offDiag A θs i₀| ≤ M * (ρ * A[i₀][i₀] * w[i₀]) :=
    (abs_offDiag_le A w θs hall i₀).trans (mul_le_mul_of_nonneg_left (hdd.dominant i₀) hM)
  have hθ₀ : |θs[i₀]| = M * w[i₀] := by
    simp only [M]; field_simp
  have key : A[i₀][i₀] * (M * w[i₀]) ≤ |b[i₀]| + M * (ρ * A[i₀][i₀] * w[i₀]) := by
    have : A[i₀][i₀] * θs[i₀] = b[i₀] - offDiag A θs i₀ := by linarith
    calc A[i₀][i₀] * (M * w[i₀]) = |A[i₀][i₀] * θs[i₀]| := by
          rw [abs_mul, abs_of_pos hA, hθ₀]
      _ = |b[i₀] - offDiag A θs i₀| := by rw [this]
      _ ≤ |b[i₀]| + |offDiag A θs i₀| := abs_sub _ _
      _ ≤ |b[i₀]| + M * (ρ * A[i₀][i₀] * w[i₀]) := by linarith
  have hMβ : M ≤ β := by
    have hc : 0 < (1 - ρ) * A[i₀][i₀] * w[i₀] :=
      mul_pos (mul_pos (by linarith [hdd.ratio_lt_one]) hA) hw₀
    have : (1 - ρ) * A[i₀][i₀] * w[i₀] * M ≤ (1 - ρ) * A[i₀][i₀] * w[i₀] * β := by
      nlinarith [hb i₀]
    exact le_of_mul_le_mul_left this hc
  exact (hall i).trans (mul_le_mul_of_nonneg_right hMβ (hdd.weight_pos i).le)

/-- From `θ = 0`, the error after `k` Jacobi steps is at most `ρᵏ β wᵢ`. -/
theorem jacobi_bound (hdd : DiagDominant A w ρ) {θs : Vec ℝ n}
    (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) {β : ℝ} (hβ : 0 ≤ β)
    (hb : ∀ i : Fin n, |b[i]| ≤ (1 - ρ) * A[i][i] * w[i] * β) (k : ℕ) (i : Fin n) :
    |(jacobi A b k)[i] - θs[i]| ≤ ρ ^ k * β * w[i] :=
  jacobi_iterate_bound hdd hsol hβ vzero
    (fun j ↦ by rw [vzero_getElem, zero_sub, abs_neg]; exact solution_bound hdd hsol hb j) k i

/-- From `θ = 0`, the error after `k` Gauss–Seidel sweeps is at most `ρᵏ β wᵢ`. -/
theorem gaussSeidel_bound (hdd : DiagDominant A w ρ) {θs : Vec ℝ n}
    (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) {β : ℝ} (hβ : 0 ≤ β)
    (hb : ∀ i : Fin n, |b[i]| ≤ (1 - ρ) * A[i][i] * w[i] * β) (k : ℕ) (i : Fin n) :
    |(gaussSeidel A b k)[i] - θs[i]| ≤ ρ ^ k * β * w[i] :=
  gaussSeidel_iterate_bound hdd hsol hβ vzero
    (fun j ↦ by rw [vzero_getElem, zero_sub, abs_neg]; exact solution_bound hdd hsol hb j) k i

/-- `vᵀ A v ≤ c² Γ` when every `|vᵢ| ≤ c wᵢ`. -/
theorem quad_le_weightedMass (hw : ∀ i : Fin n, 0 ≤ w[i]) {c : ℝ} (hc : 0 ≤ c) (v : Vec ℝ n)
    (hv : ∀ i : Fin n, |v[i]| ≤ c * w[i]) :
    ∑ i : Fin n, ∑ j : Fin n, A[i][j] * v[i] * v[j] ≤ c ^ 2 * weightedMass A w := by
  rw [weightedMass, mul_sum]
  refine sum_le_sum fun i _ ↦ ?_
  rw [mul_sum]
  refine sum_le_sum fun j _ ↦ ?_
  calc A[i][j] * v[i] * v[j] ≤ |A[i][j] * v[i] * v[j]| := le_abs_self _
    _ = |A[i][j]| * |v[i]| * |v[j]| := by rw [abs_mul, abs_mul]
    _ ≤ |A[i][j]| * (c * w[i]) * (c * w[j]) := by
        have h1 : |A[i][j]| * |v[i]| ≤ |A[i][j]| * (c * w[i]) :=
          mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
        have h2 : 0 ≤ |A[i][j]| * (c * w[i]) :=
          mul_nonneg (abs_nonneg _) (mul_nonneg hc (hw i))
        exact mul_le_mul h1 (hv j) (abs_nonneg _) h2
    _ = c ^ 2 * (|A[i][j]| * w[i] * w[j]) := by ring

end Solution

/-! ## Regression: excess loss, monotonicity, fixed points -/

namespace Problem

variable {m d : ℕ} (P : Problem ℝ m d)

/-- Excess loss of any parameters within `c wᵢ` of a solution of the normal equations. -/
theorem loss_le_of_near_solution (hridge : 0 ≤ P.ridge) {w : Vec ℝ (d + 1)}
    (hw : ∀ i : Fin (d + 1), 0 ≤ w[i]) {θs : Vec ℝ (d + 1)}
    (hsol : ∀ i : Fin (d + 1), (matVec P.normalMatrix θs)[i] = P.normalVector[i])
    {c : ℝ} (hc : 0 ≤ c) (θ : Vec ℝ (d + 1)) (hθ : ∀ i : Fin (d + 1), |θ[i] - θs[i]| ≤ c * w[i])
    (u : Vec ℝ (d + 1)) : P.loss θ ≤ P.loss u + c ^ 2 * weightedMass P.normalMatrix w := by
  have hres : ∀ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θs)[i] = 0 :=
    fun i ↦ by rw [residual, vsub_getElem, hsol i, sub_self]
  rw [P.loss_eq_of_residual_eq_zero hres θ, curvature_eq]
  have hq := quad_le_weightedMass (A := P.normalMatrix) hw hc (vsub θ θs)
    (fun i ↦ by rw [vsub_getElem]; exact hθ i)
  have hopt := P.loss_le_of_residual_eq_zero hridge hres u
  linarith

/-- **Certified Jacobi**: with weighted diagonal dominance and `|bᵢ| ≤ (1 - ρ) Aᵢᵢ wᵢ β`,
after `k` steps `L(θₖ) ≤ L(u) + Γ β² ρ²ᵏ` for every `u`. -/
theorem loss_jacobi_le (hridge : 0 ≤ P.ridge) {w : Vec ℝ (d + 1)} {ρ β : ℝ}
    (hdd : DiagDominant P.normalMatrix w ρ) (hβ : 0 ≤ β)
    (hb : ∀ i : Fin (d + 1), |P.normalVector[i]| ≤ (1 - ρ) * P.normalMatrix[i][i] * w[i] * β)
    (k : ℕ) (u : Vec ℝ (d + 1)) :
    P.loss (jacobi P.normalMatrix P.normalVector k) ≤
      P.loss u + weightedMass P.normalMatrix w * β ^ 2 * ρ ^ (2 * k) := by
  obtain ⟨θs, hsol⟩ := exists_solution hdd P.normalVector
  have hc : 0 ≤ ρ ^ k * β := mul_nonneg (pow_nonneg hdd.ratio_nonneg k) hβ
  have := P.loss_le_of_near_solution hridge (fun i ↦ (hdd.weight_pos i).le) hsol hc _
    (jacobi_bound hdd hsol hβ hb k) u
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Certified Gauss–Seidel**: the same bound after `k` sweeps. -/
theorem loss_gaussSeidel_le (hridge : 0 ≤ P.ridge) {w : Vec ℝ (d + 1)} {ρ β : ℝ}
    (hdd : DiagDominant P.normalMatrix w ρ) (hβ : 0 ≤ β)
    (hb : ∀ i : Fin (d + 1), |P.normalVector[i]| ≤ (1 - ρ) * P.normalMatrix[i][i] * w[i] * β)
    (k : ℕ) (u : Vec ℝ (d + 1)) :
    P.loss (gaussSeidel P.normalMatrix P.normalVector k) ≤
      P.loss u + weightedMass P.normalMatrix w * β ^ 2 * ρ ^ (2 * k) := by
  obtain ⟨θs, hsol⟩ := exists_solution hdd P.normalVector
  have hc : 0 ≤ ρ ^ k * β := mul_nonneg (pow_nonneg hdd.ratio_nonneg k) hβ
  have := P.loss_le_of_near_solution hridge (fun i ↦ (hdd.weight_pos i).le) hsol hc _
    (gaussSeidel_bound hdd hsol hβ hb k) u
  calc _ ≤ _ := this
    _ = _ := by ring

theorem normalMatrix_diag_nonneg (hridge : 0 ≤ P.ridge) (i : Fin (d + 1)) :
    0 ≤ P.normalMatrix[i][i] := by
  rw [normalMatrix_apply, if_pos rfl]
  exact add_nonneg (div_nonneg (sum_nonneg fun _ _ ↦ mul_self_nonneg _) (Nat.cast_nonneg m))
    hridge

/-- The unit vector `t eᵢ`. -/
noncomputable def coord (i : Fin (d + 1)) (t : ℝ) : Vec ℝ (d + 1) :=
  Vector.ofFn fun j ↦ if j = i then t else 0

theorem curvature_coord (i : Fin (d + 1)) (t : ℝ) :
    P.curvature (coord i t) = t ^ 2 * P.normalMatrix[i][i] := by
  rw [curvature_eq]
  simp only [coord, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true]
  ring

/-- **One Gauss–Seidel update never increases the loss**: it minimises the loss exactly
along coordinate `i`. -/
theorem loss_gsUpdate_le (hridge : 0 ≤ P.ridge) (θ : Vec ℝ (d + 1)) (i : Fin (d + 1)) :
    P.loss (gsUpdate P.normalMatrix P.normalVector θ i) ≤ P.loss θ := by
  set A := P.normalMatrix
  rcases (P.normalMatrix_diag_nonneg hridge i).lt_or_eq with hA | hA
  · -- the new coordinate is `θᵢ + t` with `t = -rᵢ / Aᵢᵢ`; the loss drops by `rᵢ² / Aᵢᵢ`
    have hA' : A[i][i] ≠ 0 := hA.ne'
    set t := (P.normalVector[i] - offDiag A θ i) / A[i][i] - θ[i]
    have hupd : gsUpdate A P.normalVector θ i = vadd θ (coord i t) := vext fun j ↦ by
      rw [gsUpdate_getElem, vadd_getElem, coordSolve_of_ne hA']
      simp only [coord, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
      split_ifs with h
      · subst h; simp [t]
      · simp
    rw [hupd, loss_add, curvature_coord]
    have hsum : ∑ j : Fin (d + 1), (residual A P.normalVector θ)[j] * (coord i t)[j] =
        (residual A P.normalVector θ)[i] * t := by
      simp only [coord, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, mul_ite, mul_zero,
        sum_ite_eq', mem_univ, if_true]
    rw [hsum]
    have hr : (residual A P.normalVector θ)[i] = offDiag A θ i + A[i][i] * θ[i] -
        P.normalVector[i] := by
      simp [residual, offDiag, matVec, A]
    have ht : t = -(residual A P.normalVector θ)[i] / A[i][i] := by
      rw [hr]; simp only [t]; field_simp; ring
    rw [ht]
    have : 2 * ((residual A P.normalVector θ)[i] * (-(residual A P.normalVector θ)[i] /
        A[i][i])) + (-(residual A P.normalVector θ)[i] / A[i][i]) ^ 2 * A[i][i] =
        -((residual A P.normalVector θ)[i] ^ 2 / A[i][i]) := by
      field_simp; ring
    have : 0 ≤ (residual A P.normalVector θ)[i] ^ 2 / A[i][i] := div_nonneg (sq_nonneg _) hA.le
    linarith
  · -- `Aᵢᵢ = 0`: the update keeps `θᵢ`
    have hupd : gsUpdate A P.normalVector θ i = θ := vext fun j ↦ by
      rw [gsUpdate_getElem, coordSolve_of_eq hA.symm]
      split_ifs with h
      · subst h; rfl
      · rfl
    rw [hupd]

theorem loss_foldl_gsUpdate_le (hridge : 0 ≤ P.ridge) (l : List (Fin (d + 1)))
    (θ : Vec ℝ (d + 1)) :
    P.loss (l.foldl (gsUpdate P.normalMatrix P.normalVector) θ) ≤ P.loss θ := by
  induction l generalizing θ with
  | nil => exact le_rfl
  | cons i l ih => exact (ih _).trans (P.loss_gsUpdate_le hridge θ i)

/-- **Gauss–Seidel never increases the loss**, for any data and any `λ ≥ 0`. -/
theorem loss_gaussSeidel_antitone (hridge : 0 ≤ P.ridge) :
    Antitone fun k ↦ P.loss (gaussSeidel P.normalMatrix P.normalVector k) := by
  refine antitone_nat_of_succ_le fun k ↦ ?_
  simp only [gaussSeidel]
  rw [Function.iterate_succ_apply']
  exact P.loss_foldl_gsUpdate_le hridge _ _

/-- **A fixed point of Jacobi solves the normal equations**, so it minimises the loss. -/
theorem loss_le_of_jacobiStep_eq_self (hridge : 0 ≤ P.ridge) {θ : Vec ℝ (d + 1)}
    (hfix : jacobiStep P.normalMatrix P.normalVector θ = θ) (u : Vec ℝ (d + 1)) :
    P.loss θ ≤ P.loss u := by
  refine P.loss_le_of_residual_eq_zero hridge (fun i ↦ ?_) u
  rcases (P.normalMatrix_diag_nonneg hridge i).lt_or_eq with hA | hA
  · have h := congrArg (·[i]) hfix
    simp only [jacobiStep_getElem, coordSolve_of_ne hA.ne'] at h
    rw [div_eq_iff hA.ne'] at h
    simp [residual, matVec, offDiag] at h ⊢
    linarith
  · exact P.residual_eq_zero_of_diag_eq_zero hridge hA.symm θ

end Problem

end LeanLearn.Regression
