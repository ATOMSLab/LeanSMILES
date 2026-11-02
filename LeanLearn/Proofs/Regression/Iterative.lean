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

-- a sum over `j ≠ i` written with an `if` (the shape of `offDiag` and `offDiagWeight`) is the
-- sum over `univ.erase i` (the shape Gershgorin's theorem and `sum_erase_eq_sub` use)
private theorem sum_ite_eq_sum_erase (f : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, (if j = i then 0 else f j) = ∑ j ∈ univ.erase i, f j := by
  rw [← sum_erase_add _ _ (mem_univ i), if_pos rfl, add_zero]
  exact sum_congr rfl fun j hj ↦ if_neg (ne_of_mem_erase hj)

/-- `∑_{j≠i} |Aᵢⱼ| wⱼ`: what row `i` of `A` can move the other coordinates by, in the weighted
norm. -/
noncomputable def offDiagWeight (A : Mat ℝ n n) (w : Vec ℝ n) (i : Fin n) : ℝ :=
  ∑ j : Fin n, if j = i then 0 else |A[i][j]| * w[j]

/-- `Γ = ∑ᵢⱼ |Aᵢⱼ| wᵢ wⱼ`: the constant in the excess-loss bounds `loss_jacobi_le` and
`loss_gaussSeidel_le`. -/
noncomputable def weightedMass (A : Mat ℝ n n) (w : Vec ℝ n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, |A[i][j]| * w[i] * w[j]

/-- **Weighted diagonal dominance** with weights `w` and ratio `ρ`: `w = 1` is strict diagonal
dominance, and other weights certify more matrices. -/
structure DiagDominant (A : Mat ℝ n n) (w : Vec ℝ n) (ρ : ℝ) : Prop where
  /-- The contraction ratio is non-negative. -/
  ratio_nonneg : 0 ≤ ρ
  /-- The contraction ratio is below `1`: this is what makes the iterations converge. -/
  ratio_lt_one : ρ < 1
  /-- Every weight is positive. -/
  weight_pos : ∀ i : Fin n, 0 < w[i]
  /-- Every diagonal entry is positive, so every coordinate update divides by it. -/
  diag_pos : ∀ i : Fin n, 0 < A[i][i]
  /-- Row `i`: `∑_{j≠i} |Aᵢⱼ| wⱼ ≤ ρ Aᵢᵢ wᵢ`. -/
  dominant : ∀ i : Fin n, offDiagWeight A w i ≤ ρ * A[i][i] * w[i]

/-- Row `i` of `A` dotted with `θ`, as a `Finset` sum: `dot_eq_sum` at a matrix row. -/
theorem dot_getElem_eq (A : Mat ℝ n n) (θ : Vec ℝ n) (i : Fin n) :
    dot A[i] θ = ∑ j : Fin n, A[i][j] * θ[j] := dot_eq_sum _ _

/-- `∑_{j≠i} Aᵢⱼ θⱼ` as a `Finset` sum with the diagonal term zeroed by an `if`. -/
theorem offDiag_eq_sum (A : Mat ℝ n n) (θ : Vec ℝ n) (i : Fin n) :
    offDiag A θ i = ∑ j : Fin n, if j = i then 0 else A[i][j] * θ[j] := by
  rw [offDiag, dot_getElem_eq, sum_ite_eq_sum_erase, sum_erase_eq_sub (mem_univ i)]

/-- The off-diagonal sum is linear: `offDiag` of a difference is the difference of `offDiag`s. -/
theorem offDiag_sub (A : Mat ℝ n n) (θ θ' : Vec ℝ n) (i : Fin n) :
    offDiag A θ i - offDiag A θ' i = offDiag A (vsub θ θ') i := by
  simp only [offDiag_eq_sum, ← sum_sub_distrib, vsub_getElem]
  exact sum_congr rfl fun j _ ↦ by split_ifs <;> ring

/-- If every `|eⱼ| ≤ M wⱼ`, then `|∑_{j≠i} Aᵢⱼ eⱼ| ≤ M ∑_{j≠i} |Aᵢⱼ| wⱼ`: the off-diagonal sum
is controlled by `offDiagWeight` in the weighted norm. -/
theorem abs_offDiag_le (A : Mat ℝ n n) (w e : Vec ℝ n) {M : ℝ} (he : ∀ j : Fin n, |e[j]| ≤ M * w[j])
    (i : Fin n) : |offDiag A e i| ≤ M * offDiagWeight A w i := by
  rw [offDiag_eq_sum, offDiagWeight, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
  split_ifs
  · simp
  · rw [abs_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (he j) (abs_nonneg _)

/-! ## One coordinate update -/

/-- When `Aᵢᵢ ≠ 0`, `coordSolve` solves equation `i` for coordinate `i`. -/
theorem coordSolve_of_ne {A : Mat ℝ n n} {b θ : Vec ℝ n} {i : Fin n} (hA : A[i][i] ≠ 0) :
    coordSolve A b θ i = (b[i] - offDiag A θ i) / A[i][i] := by
  rw [coordSolve, if_neg (by simpa using hA)]

/-- When `Aᵢᵢ = 0`, `coordSolve` keeps coordinate `i`. -/
theorem coordSolve_of_eq {A : Mat ℝ n n} {b θ : Vec ℝ n} {i : Fin n} (hA : A[i][i] = 0) :
    coordSolve A b θ i = θ[i] := by
  rw [coordSolve, if_pos (by simpa using hA)]

section Update

variable {A : Mat ℝ n n} {b θs : Vec ℝ n}

-- the residual of row `i`, with the diagonal term split off
private theorem residual_getElem_eq (θ : Vec ℝ n) (i : Fin n) :
    (residual A b θ)[i] = offDiag A θ i + A[i][i] * θ[i] - b[i] := by
  simp [residual, offDiag, matVec]

-- `coordSolve` moves coordinate `i` by `t` with `Aᵢᵢ t = -rᵢ`: the step cancels the residual
private theorem residual_getElem_eq_neg_mul (θ : Vec ℝ n) {i : Fin n} (hA : A[i][i] ≠ 0) :
    (residual A b θ)[i] = -(A[i][i] * (coordSolve A b θ i - θ[i])) := by
  rw [coordSolve_of_ne hA, residual_getElem_eq, mul_sub, mul_div_cancel₀ _ hA]
  ring

/-- A solution satisfies `bᵢ = ∑_{j≠i} Aᵢⱼ θ*ⱼ + Aᵢᵢ θ*ᵢ`. -/
theorem solution_row (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) (i : Fin n) :
    b[i] = offDiag A θs i + A[i][i] * θs[i] := by
  simp [← hsol i, offDiag, matVec]

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

/-- Entry `i` of a Jacobi step is `coordSolve` at `i`: every coordinate is updated from the old
`θ`. -/
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
    simpa only [Function.iterate_succ_apply', pow_succ', mul_assoc] using
      jacobiStep_bound hdd hsol (mul_nonneg (pow_nonneg hdd.ratio_nonneg k) hM) _ ih i

end Jacobi

/-! ## Gauss–Seidel -/

section GaussSeidel

variable {A : Mat ℝ n n} {b θs w : Vec ℝ n} {ρ : ℝ}

/-- A Gauss–Seidel update changes coordinate `i` to `coordSolve` at `i` and keeps the others. -/
theorem gsUpdate_getElem (θ : Vec ℝ n) (i j : Fin n) :
    (gsUpdate A b θ i)[j] = if j = i then coordSolve A b θ i else θ[j] := by
  grind [gsUpdate]

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
    have hnew : |coordSolve A b θ i - θs[i]| ≤ ρ * M * w[i] :=
      coordSolve_of_ne (hdd.diag_pos i).ne' ▸ update_bound hdd hsol hM θ hθ i
    have hρM : ρ * M * w[i] ≤ M * w[i] :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hM hdd.ratio_lt_one.le)
        (hdd.weight_pos i).le
    have hθ' : ∀ j : Fin n, |(gsUpdate A b θ i)[j] - θs[j]| ≤ M * w[j] := fun j ↦ by
      obtain rfl | h := eq_or_ne j i
      · simpa only [gsUpdate_getElem, if_pos rfl] using hnew.trans hρM
      · simpa only [gsUpdate_getElem, if_neg h] using hθ j
    have hdone' : ∀ j, (done j ∨ j = i) → |(gsUpdate A b θ i)[j] - θs[j]| ≤ ρ * M * w[j] :=
      fun j hj ↦ by
        obtain rfl | h := eq_or_ne j i
        · simpa only [gsUpdate_getElem, if_pos rfl] using hnew
        · simpa only [gsUpdate_getElem, if_neg h] using hdone j (hj.resolve_right h)
    obtain ⟨h1, h2⟩ := ih (gsUpdate A b θ i) (fun j ↦ done j ∨ j = i) hθ' hdone'
    exact ⟨h1, fun j hj ↦ h2 j (by simpa only [List.mem_cons, or_assoc] using hj)⟩

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
    simpa only [Function.iterate_succ_apply', pow_succ', mul_assoc] using
      gsSweep_bound hdd hsol (mul_nonneg (pow_nonneg hdd.ratio_nonneg k) hM) _ ih i

end GaussSeidel

/-! ## The solution: existence and size -/

section Solution

variable {A : Mat ℝ n n} {b w : Vec ℝ n} {ρ : ℝ}

/-- The matrix as Mathlib sees it, so that Gershgorin's theorem and the inverse apply. -/
noncomputable def toMatrix (A : Mat ℝ n n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦ A[i][j]

/-- **Weighted diagonal dominance makes `A` invertible**: scaling column `j` by `wⱼ` gives a
strictly diagonally dominant matrix, whose determinant Gershgorin's theorem keeps away from
`0`. -/
theorem det_ne_zero (hdd : DiagDominant A w ρ) : (toMatrix A).det ≠ 0 := by
  -- scale column `j` by `wⱼ`: the result is strictly diagonally dominant
  have hB : (toMatrix A * Matrix.diagonal fun j : Fin n ↦ w[j]).det ≠ 0 := by
    refine det_ne_zero_of_sum_row_lt_diag fun i ↦ ?_
    have hentry : ∀ j, (toMatrix A * Matrix.diagonal fun j : Fin n ↦ w[j]) i j = A[i][j] * w[j] :=
      fun j ↦ by simp [toMatrix, Matrix.mul_diagonal]
    simp only [hentry, Real.norm_eq_abs, abs_mul, abs_of_pos (hdd.weight_pos _),
      abs_of_pos (hdd.diag_pos i), ← sum_ite_eq_sum_erase]
    exact (hdd.dominant i).trans_lt <| by
      nlinarith [mul_pos (hdd.diag_pos i) (hdd.weight_pos i), hdd.ratio_lt_one]
  rw [Matrix.det_mul] at hB
  exact left_ne_zero_of_mul hB

/-- **A solution exists** when `A` is weighted diagonally dominant. -/
theorem exists_solution (hdd : DiagDominant A w ρ) (b : Vec ℝ n) :
    ∃ θs : Vec ℝ n, ∀ i : Fin n, (matVec A θs)[i] = b[i] := by
  let v : Fin n → ℝ := (toMatrix A)⁻¹.mulVec fun j ↦ b[j]
  have h : (toMatrix A).mulVec v = fun j ↦ b[j] := by
    simp only [v, Matrix.mulVec_mulVec, Matrix.one_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_ne_zero hdd))]
  refine ⟨Vector.ofFn v, fun i ↦ ?_⟩
  rw [matVec_getElem]
  simpa [toMatrix, Matrix.mulVec, dotProduct] using congrFun h i

/-- **The size of the solution**: if `|bᵢ| ≤ (1 - ρ) Aᵢᵢ wᵢ β` for every row, then
`|θ*ᵢ| ≤ β wᵢ`. -/
theorem solution_bound (hdd : DiagDominant A w ρ) {θs : Vec ℝ n}
    (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) {β : ℝ}
    (hb : ∀ i : Fin n, |b[i]| ≤ (1 - ρ) * A[i][i] * w[i] * β) (i : Fin n) :
    |θs[i]| ≤ β * w[i] := by
  -- the coordinate where `|θ*ⱼ| / wⱼ` is largest
  obtain ⟨i₀, -, hmax⟩ := exists_max_image univ (fun j : Fin n ↦ |θs[j]| / w[j]) ⟨i, mem_univ i⟩
  set M := |θs[i₀]| / w[i₀]
  have hw₀ := hdd.weight_pos i₀
  have hall : ∀ j : Fin n, |θs[j]| ≤ M * w[j] := fun j ↦
    (div_le_iff₀ (hdd.weight_pos j)).mp (hmax j (mem_univ j))
  have hM : 0 ≤ M := div_nonneg (abs_nonneg _) hw₀.le
  -- row `i₀`: `Aᵢᵢ |θ*ᵢ| ≤ |bᵢ| + ρ Aᵢᵢ wᵢ M`
  have hA := hdd.diag_pos i₀
  have hoff : |offDiag A θs i₀| ≤ M * (ρ * A[i₀][i₀] * w[i₀]) :=
    (abs_offDiag_le A w θs hall i₀).trans (mul_le_mul_of_nonneg_left (hdd.dominant i₀) hM)
  have hθ₀ : |θs[i₀]| = M * w[i₀] := (div_mul_cancel₀ _ hw₀.ne').symm
  have key : A[i₀][i₀] * (M * w[i₀]) ≤ |b[i₀]| + M * (ρ * A[i₀][i₀] * w[i₀]) := by
    calc A[i₀][i₀] * (M * w[i₀]) = |b[i₀] - offDiag A θs i₀| := by
          rw [← hθ₀, ← abs_of_pos hA, ← abs_mul, solution_row hsol i₀, add_sub_cancel_left]
      _ ≤ |b[i₀]| + |offDiag A θs i₀| := abs_sub _ _
      _ ≤ |b[i₀]| + M * (ρ * A[i₀][i₀] * w[i₀]) := by linarith
  have hMβ : M ≤ β :=
    le_of_mul_le_mul_left (by linarith [key, hb i₀])
      (mul_pos (mul_pos (sub_pos.mpr hdd.ratio_lt_one) hA) hw₀)
  exact (hall i).trans (mul_le_mul_of_nonneg_right hMβ (hdd.weight_pos i).le)

/-- From `θ = 0`, the error after `k` Jacobi steps is at most `ρᵏ β wᵢ`. -/
theorem jacobi_bound (hdd : DiagDominant A w ρ) {θs : Vec ℝ n}
    (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) {β : ℝ} (hβ : 0 ≤ β)
    (hb : ∀ i : Fin n, |b[i]| ≤ (1 - ρ) * A[i][i] * w[i] * β) (k : ℕ) (i : Fin n) :
    |(jacobi A b k)[i] - θs[i]| ≤ ρ ^ k * β * w[i] :=
  jacobi_iterate_bound hdd hsol hβ vzero (fun j ↦ by simpa using solution_bound hdd hsol hb j) k i

/-- From `θ = 0`, the error after `k` Gauss–Seidel sweeps is at most `ρᵏ β wᵢ`. -/
theorem gaussSeidel_bound (hdd : DiagDominant A w ρ) {θs : Vec ℝ n}
    (hsol : ∀ i : Fin n, (matVec A θs)[i] = b[i]) {β : ℝ} (hβ : 0 ≤ β)
    (hb : ∀ i : Fin n, |b[i]| ≤ (1 - ρ) * A[i][i] * w[i] * β) (k : ℕ) (i : Fin n) :
    |(gaussSeidel A b k)[i] - θs[i]| ≤ ρ ^ k * β * w[i] :=
  gaussSeidel_iterate_bound hdd hsol hβ vzero
    (fun j ↦ by simpa using solution_bound hdd hsol hb j) k i

/-- `vᵀ A v ≤ c² Γ` when every `|vᵢ| ≤ c wᵢ`: the quadratic form of `A` on a vector within
`c wᵢ` of `0` is at most `c²` times the weighted mass. -/
theorem quad_le_weightedMass {c : ℝ} (v : Vec ℝ n) (hv : ∀ i : Fin n, |v[i]| ≤ c * w[i]) :
    ∑ i : Fin n, ∑ j : Fin n, A[i][j] * v[i] * v[j] ≤ c ^ 2 * weightedMass A w := by
  simp only [weightedMass, mul_sum]
  refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
  calc A[i][j] * v[i] * v[j] ≤ |A[i][j]| * |v[i]| * |v[j]| :=
        (le_abs_self _).trans_eq (by rw [abs_mul, abs_mul])
    _ ≤ |A[i][j]| * (c * w[i]) * (c * w[j]) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)) (hv j) (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans (hv i)))
    _ = c ^ 2 * (|A[i][j]| * w[i] * w[j]) := by ring

end Solution

/-! ## Regression: excess loss, monotonicity, fixed points -/

namespace Problem

variable {m d : ℕ} (P : Problem ℝ m d)

/-- Excess loss of any parameters within `c wᵢ` of a solution of the normal equations. -/
theorem loss_le_of_near_solution (hridge : 0 ≤ P.ridge) {w θs : Vec ℝ (d + 1)}
    (hsol : ∀ i : Fin (d + 1), (matVec P.normalMatrix θs)[i] = P.normalVector[i]) {c : ℝ}
    (θ : Vec ℝ (d + 1)) (hθ : ∀ i : Fin (d + 1), |θ[i] - θs[i]| ≤ c * w[i]) (u : Vec ℝ (d + 1)) :
    P.loss θ ≤ P.loss u + c ^ 2 * weightedMass P.normalMatrix w := by
  have hres : ∀ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θs)[i] = 0 :=
    fun i ↦ by rw [residual, vsub_getElem, hsol i, sub_self]
  rw [P.loss_eq_of_residual_eq_zero hres θ, curvature_eq]
  have hq := quad_le_weightedMass (A := P.normalMatrix) (w := w) (c := c) (vsub θ θs)
    fun i ↦ by simpa using hθ i
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
  exact (P.loss_le_of_near_solution hridge hsol _ (jacobi_bound hdd hsol hβ hb k) u).trans_eq
    (by ring)

/-- **Certified Gauss–Seidel**: the same bound after `k` sweeps. -/
theorem loss_gaussSeidel_le (hridge : 0 ≤ P.ridge) {w : Vec ℝ (d + 1)} {ρ β : ℝ}
    (hdd : DiagDominant P.normalMatrix w ρ) (hβ : 0 ≤ β)
    (hb : ∀ i : Fin (d + 1), |P.normalVector[i]| ≤ (1 - ρ) * P.normalMatrix[i][i] * w[i] * β)
    (k : ℕ) (u : Vec ℝ (d + 1)) :
    P.loss (gaussSeidel P.normalMatrix P.normalVector k) ≤
      P.loss u + weightedMass P.normalMatrix w * β ^ 2 * ρ ^ (2 * k) := by
  obtain ⟨θs, hsol⟩ := exists_solution hdd P.normalVector
  exact (P.loss_le_of_near_solution hridge hsol _ (gaussSeidel_bound hdd hsol hβ hb k)
    u).trans_eq (by ring)

/-- The diagonal of the normal matrix is non-negative for `λ ≥ 0`: `Aᵢᵢ = (1/m) ∑ᵣ xᵣᵢ² + λ`. -/
theorem normalMatrix_diag_nonneg (hridge : 0 ≤ P.ridge) (i : Fin (d + 1)) :
    0 ≤ P.normalMatrix[i][i] := by
  rw [normalMatrix_apply, if_pos rfl]
  exact add_nonneg (div_nonneg (sum_nonneg fun _ _ ↦ mul_self_nonneg _) (Nat.cast_nonneg m))
    hridge

/-- The vector `t eᵢ`: `t` at coordinate `i` and `0` elsewhere, the direction of one Gauss–Seidel
update. -/
noncomputable def coord (i : Fin (d + 1)) (t : ℝ) : Vec ℝ (d + 1) :=
  Vector.ofFn fun j ↦ if j = i then t else 0

-- entry `j` of `t eᵢ`
private theorem coord_getElem (i : Fin (d + 1)) (t : ℝ) (j : Fin (d + 1)) :
    (coord i t)[j] = if j = i then t else 0 := by
  simp [coord]

-- `⟪v, t eᵢ⟫ = vᵢ t`
private theorem sum_mul_coord (v : Vec ℝ (d + 1)) (i : Fin (d + 1)) (t : ℝ) :
    ∑ j : Fin (d + 1), v[j] * (coord i t)[j] = v[i] * t := by
  simp only [coord_getElem, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]

/-- The curvature along coordinate `i` is `Aᵢᵢ`: `C(t eᵢ) = t² Aᵢᵢ`. -/
theorem curvature_coord (i : Fin (d + 1)) (t : ℝ) :
    P.curvature (coord i t) = t ^ 2 * P.normalMatrix[i][i] := by
  simp only [curvature_eq, coord_getElem, mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq',
    mem_univ, if_true]
  ring

-- a Gauss–Seidel update moves along coordinate `i`, by `coordSolve` minus the old value
private theorem gsUpdate_eq_vadd_coord {A : Mat ℝ (d + 1) (d + 1)} {b : Vec ℝ (d + 1)}
    (θ : Vec ℝ (d + 1)) (i : Fin (d + 1)) :
    gsUpdate A b θ i = vadd θ (coord i (coordSolve A b θ i - θ[i])) := vext fun j ↦ by
  rw [gsUpdate_getElem, vadd_getElem, coord_getElem]
  split_ifs with h
  · rw [h, add_sub_cancel]
  · rw [add_zero]

/-- **One Gauss–Seidel update never increases the loss**: it minimises the loss exactly
along coordinate `i`. -/
theorem loss_gsUpdate_le (hridge : 0 ≤ P.ridge) (θ : Vec ℝ (d + 1)) (i : Fin (d + 1)) :
    P.loss (gsUpdate P.normalMatrix P.normalVector θ i) ≤ P.loss θ := by
  rw [gsUpdate_eq_vadd_coord, loss_add, curvature_coord, sum_mul_coord]
  rcases (P.normalMatrix_diag_nonneg hridge i).lt_or_eq with hA | hA
  · -- the new coordinate is `θᵢ + t` with `Aᵢᵢ t = -rᵢ`, i.e. `t = -rᵢ / Aᵢᵢ`; the loss drops by
    -- `Aᵢᵢ t² = rᵢ² / Aᵢᵢ`
    rw [residual_getElem_eq_neg_mul θ hA.ne']
    linarith [mul_nonneg hA.le (sq_nonneg (coordSolve P.normalMatrix P.normalVector θ i - θ[i]))]
  · -- `Aᵢᵢ = 0`: the update keeps `θᵢ`
    simp [coordSolve_of_eq hA.symm]

/-- Gauss–Seidel updates along any list of coordinates never increase the loss. -/
theorem loss_foldl_gsUpdate_le (hridge : 0 ≤ P.ridge) (l : List (Fin (d + 1))) (θ : Vec ℝ (d + 1)) :
    P.loss (l.foldl (gsUpdate P.normalMatrix P.normalVector) θ) ≤ P.loss θ := by
  induction l generalizing θ with
  | nil => exact le_rfl
  | cons i l ih => exact (ih _).trans (P.loss_gsUpdate_le hridge θ i)

/-- **Gauss–Seidel never increases the loss**, for any data and any `λ ≥ 0`. -/
theorem loss_gaussSeidel_antitone (hridge : 0 ≤ P.ridge) :
    Antitone fun k ↦ P.loss (gaussSeidel P.normalMatrix P.normalVector k) := by
  refine antitone_nat_of_succ_le fun k ↦ ?_
  simp only [gaussSeidel, Function.iterate_succ_apply']
  exact P.loss_foldl_gsUpdate_le hridge _ _

/-- **A fixed point of Jacobi solves the normal equations**, so it minimises the loss. -/
theorem loss_le_of_jacobiStep_eq_self (hridge : 0 ≤ P.ridge) {θ : Vec ℝ (d + 1)}
    (hfix : jacobiStep P.normalMatrix P.normalVector θ = θ) (u : Vec ℝ (d + 1)) :
    P.loss θ ≤ P.loss u := by
  refine P.loss_le_of_residual_eq_zero hridge (fun i ↦ ?_) u
  rcases (P.normalMatrix_diag_nonneg hridge i).lt_or_eq with hA | hA
  · have h := congrArg (·[i]) hfix
    simp only [jacobiStep_getElem] at h
    rw [residual_getElem_eq_neg_mul θ hA.ne', h, sub_self, mul_zero, neg_zero]
  · exact P.residual_eq_zero_of_diag_eq_zero hridge hA.symm θ

end Problem

end LeanLearn.Regression
