/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanLearn.Regression.SparseProblem
public import LeanLearn.Proofs.Regression.Certificates
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# LeanLearn.Proofs.Regression.SparseProblem

The sparse residual is the dense residual.

* **The dense residual, entrywise, over `ℚ`** (`Problem.residualAt_apply`): the executable
  `Problem.residualAt` is `(1/m) Σᵣ xᵣᵢ (⟪xᵣ, θ⟫ − yᵣ) + λ θᵢ` — `residual_apply` of
  `Proofs/Regression/Basic.lean`, which is over `ℝ`, read in the exact arithmetic the
  certificate runs in.
* **Scatter-add is `Xᵀ v`** (`SparseProblem.scatter_getElem`) and **a sum over a bit list is a
  sum over bits weighted by counts** (`SparseProblem.sumGen_count`).
* **The sparse computations are the dense ones** (`errors_getElem`, `residual_eq`, `loss_eq`,
  `checkResidual_eq`): entry by entry, `SparseProblem.residual` is `Problem.residualAt` of
  `SparseProblem.toProblem`.
* **Soundness** (`SparseProblem.checkResidual_sound`): `Problem.checkResidual_sound`,
  verbatim.
-/

@[expose] public section

namespace LeanLearn.Regression

open Finset

/-! ## Sums over `ℚ` -/

theorem sumGen_eq_rat {X : Type*} (l : List X) (f : X → ℚ) : sumGen l f = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [sumGen, List.foldr_cons]; rw [sumGen] at ih; simp [ih]

/-- At `ℚ`, the executable sum over `Fin n` is the `Finset` sum. -/
theorem sumFin_eq_sum_rat {n : ℕ} (f : Fin n → ℚ) : sumFin f = ∑ i, f i := by
  rw [sumFin, sumGen_eq_rat, Fin.sum_univ_def]

@[simp] theorem count_rat (k : ℕ) : (count k : ℚ) = k := by
  induction k with
  | zero => simp [count, nsmulGen]
  | succ k ih =>
    simp only [count, nsmulGen] at ih ⊢
    push_cast
    rw [ih, add_comm]

section Rat

variable {n : ℕ}

theorem dot_eq_sum_rat (u v : Vec ℚ n) : dot u v = ∑ i : Fin n, u[i] * v[i] :=
  sumFin_eq_sum_rat _

theorem matVec_getElem_rat {k : ℕ} (A : Mat ℚ k n) (v : Vec ℚ n) (i : Fin k) :
    (matVec A v)[i] = ∑ j : Fin n, A[i][j] * v[j] := by
  simp [matVec, dot_eq_sum_rat]

theorem vsub_getElem_rat (u v : Vec ℚ n) (i : Fin n) : (vsub u v)[i] = u[i] - v[i] := by
  simp [vsub]

theorem vext_rat {u v : Vec ℚ n} (h : ∀ i : Fin n, u[i] = v[i]) : u = v := by
  ext i hi
  exact h ⟨i, hi⟩

end Rat

/-! ## The dense residual, entrywise, over `ℚ` -/

namespace Problem

variable {m d : ℕ} (P : Problem ℚ m d)

theorem normalMatrix_apply_rat (i j : Fin (d + 1)) :
    P.normalMatrix[i][j] =
      (∑ r : Fin m, (P.row r)[i] * (P.row r)[j]) / m + if i = j then P.ridge else 0 := by
  simp [normalMatrix, design, sumFin_eq_sum_rat]

theorem normalVector_apply_rat (i : Fin (d + 1)) :
    P.normalVector[i] = (∑ r : Fin m, (P.row r)[i] * P.y[r]) / m := by
  simp [normalVector, design, sumFin_eq_sum_rat]

/-- `∑ⱼ (∑ᵣ xᵣᵢ xᵣⱼ) θⱼ = ∑ᵣ xᵣᵢ ⟪xᵣ, θ⟫`. -/
theorem sum_gram_mul_rat (i : Fin (d + 1)) (θ : Vec ℚ (d + 1)) :
    ∑ j : Fin (d + 1), (∑ r : Fin m, (P.row r)[i] * (P.row r)[j]) * θ[j] =
      ∑ r : Fin m, (P.row r)[i] * dot (P.row r) θ := by
  simp only [dot_eq_sum_rat, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun r _ ↦ sum_congr rfl fun j _ ↦ by ring

/-- The exact residual of the normal equations at `θ`, entrywise:
`(A θ − b)ᵢ = (1/m) Σᵣ xᵣᵢ (⟪xᵣ, θ⟫ − yᵣ) + λ θᵢ`. -/
theorem residualAt_apply (θ : Vec ℚ (d + 1)) (i : Fin (d + 1)) :
    (P.residualAt θ)[i] =
      (∑ r : Fin m, (P.row r)[i] * (dot (P.row r) θ - P.y[r])) / m + P.ridge * θ[i] := by
  rw [residualAt, residual, vsub_getElem_rat, matVec_getElem_rat, normalVector_apply_rat]
  have hA : ∀ j : Fin (d + 1), P.normalMatrix[i][j] * θ[j] =
      (∑ r : Fin m, (P.row r)[i] * (P.row r)[j]) * θ[j] / m +
        if i = j then P.ridge * θ[j] else 0 := fun j ↦ by
    rw [normalMatrix_apply_rat]
    split_ifs <;> ring
  rw [sum_congr rfl fun j _ ↦ hA j, sum_add_distrib, sum_ite_eq, if_pos (mem_univ _),
    ← sum_div, sum_gram_mul_rat]
  simp only [mul_sub, sum_sub_distrib]
  ring

end Problem

/-! ## The sparse computations are the dense ones -/

namespace SparseProblem

variable {m d : ℕ}

theorem addAt_getElem (acc : Vec ℚ d) (c : ℚ) (l : List (Fin d)) (i : Fin d) :
    (addAt acc c l)[i] = acc[i] + (l.count i : ℚ) * c := by
  induction l generalizing acc with
  | nil => simp [addAt]
  | cons j l ih =>
    rw [addAt, List.foldl_cons, ← addAt, ih, List.count_cons]
    by_cases h : j = i
    · subst h
      simp only [Fin.getElem_fin, Vector.getElem_set_self, beq_self_eq_true, if_true]
      push_cast
      ring
    · have h' : (j : ℕ) ≠ i := fun e ↦ h (Fin.ext e)
      simp only [Fin.getElem_fin, Vector.getElem_set_ne _ _ h', beq_iff_eq, if_neg h,
        add_zero]

/-- Scatter-add over the rows is `Xᵀ v`. -/
theorem scatter_getElem (bits : Vector (List (Fin d)) m) (v : Vec ℚ m) (i : Fin d) :
    (scatter bits v)[i] = ∑ r : Fin m, (bits[r].count i : ℚ) * v[r] := by
  have key : ∀ (rs : List (Fin m)) (acc : Vec ℚ d),
      (rs.foldl (fun acc r ↦ addAt acc v[r] bits[r]) acc)[i] =
        acc[i] + (rs.map fun r ↦ (bits[r].count i : ℚ) * v[r]).sum := by
    intro rs
    induction rs with
    | nil => intro acc; simp
    | cons r rs ih =>
      intro acc
      rw [List.foldl_cons, ih, addAt_getElem, List.map_cons, List.sum_cons]
      ring
  rw [scatter, key, Fin.sum_univ_def]
  simp [vzero]

/-- The same with a natural-number index, the form `simp` normalises to. -/
@[simp] theorem scatter_getElem' (bits : Vector (List (Fin d)) m) (v : Vec ℚ m) (i : ℕ)
    (h : i < d) : (scatter bits v)[i] = ∑ r : Fin m, (bits[r].count ⟨i, h⟩ : ℚ) * v[r] :=
  scatter_getElem bits v ⟨i, h⟩

/-- A sum over a bit list is a sum over the bits, weighted by their counts. -/
theorem sumGen_count (l : List (Fin d)) (f : Fin d → ℚ) :
    sumGen l f = ∑ j : Fin d, (l.count j : ℚ) * f j := by
  induction l with
  | nil => simp [sumGen]
  | cons a l ih =>
    rw [sumGen, List.foldr_cons, ← sumGen, ih]
    simp only [List.count_cons, beq_iff_eq]
    push_cast
    simp only [add_mul, sum_add_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ,
      if_true]
    ring

variable (S : SparseProblem m d)

@[simp] theorem toProblem_ridge : S.toProblem.ridge = S.ridge := rfl

theorem toProblem_y (r : Fin m) : S.toProblem.y[r] = S.y[r] - S.yMean := by
  simp [toProblem]

theorem means_getElem (j : Fin d) :
    S.means[j] = (∑ r : Fin m, (S.bits[r].count j : ℚ)) / m := by
  simp [means]

theorem row_castSucc (r : Fin m) (j : Fin d) :
    (S.toProblem.row r)[j.castSucc] = (S.bits[r].count j : ℚ) - S.means[j] := by
  simp [Problem.row, augment, toProblem]

theorem row_last (r : Fin m) : (S.toProblem.row r)[Fin.last d] = 1 := by
  simp [Problem.row, augment, toProblem]

/-! The same with natural-number indices. -/

theorem row_castSucc' (r : Fin m) (j : Fin d) :
    (S.toProblem.row r)[(j : ℕ)] = (S.bits[r].count j : ℚ) - S.means[j] := by
  simp [Problem.row, augment, toProblem]

theorem row_last' (r : Fin m) : (S.toProblem.row r)[d] = 1 := by
  simp [Problem.row, augment, toProblem]

theorem fitted_eq (θ : Vec ℚ (d + 1)) (r : Fin m) :
    dot (S.toProblem.row r) θ =
      ∑ j : Fin d, ((S.bits[r].count j : ℚ) - S.means[j]) * θ[j.castSucc] + θ[Fin.last d] := by
  rw [dot_eq_sum_rat, Fin.sum_univ_castSucc]
  simp only [row_castSucc, row_last, one_mul]

/-- The sparse errors are the dense ones: `⟪xᵣ, θ⟫ − yᵣ` on the centred problem. -/
theorem errors_getElem (θ : Vec ℚ (d + 1)) (r : Fin m) :
    (S.errors θ)[r] = dot (S.toProblem.row r) θ - S.toProblem.y[r] := by
  rw [fitted_eq, toProblem_y]
  simp only [errors, Fin.getElem_fin, Vector.getElem_ofFn, sumGen_count, sumFin_eq_sum_rat,
    sub_mul, sum_sub_distrib]

/-- **The sparse residual is the dense residual.** -/
theorem residual_eq (θ : Vec ℚ (d + 1)) : S.residual θ = S.toProblem.residualAt θ := by
  refine vext_rat fun i ↦ ?_
  rw [Problem.residualAt_apply]
  simp only [← errors_getElem]
  induction i using Fin.lastCases with
  | last =>
    simp only [residual, Fin.getElem_fin, Fin.val_last, Vector.getElem_push_eq, row_last',
      one_mul, sumFin_eq_sum_rat, toProblem_ridge]
  | cast j =>
    simp only [residual, Fin.getElem_fin, Fin.val_castSucc, Fin.is_lt, Vector.getElem_push_lt,
      Vector.getElem_ofFn, Fin.eta, scatter_getElem', row_castSucc', sumFin_eq_sum_rat,
      toProblem_ridge, sub_mul, sum_sub_distrib, mul_sum]

/-- The sparse loss is the dense loss. -/
theorem loss_eq (θ : Vec ℚ (d + 1)) : S.loss θ = S.toProblem.loss θ := by
  simp only [loss, Problem.loss, errors_getElem, toProblem_ridge, count_rat]

theorem residualExcess_eq (θ : Vec ℚ (d + 1)) :
    S.residualExcess θ = S.toProblem.residualExcess θ := by
  simp only [residualExcess, Problem.residualExcess, residual_eq, toProblem_ridge]

/-- The sparse check is the dense check. -/
theorem checkResidual_eq (θ : Vec ℚ (d + 1)) (ε : ℚ) :
    S.checkResidual θ ε = S.toProblem.checkResidual θ ε := by
  simp only [checkResidual, Problem.checkResidual, residual_eq, toProblem_ridge]
  rfl

/-- **Soundness of the sparse residual check**: if it passes, the cast of `θ` is within `ε`
of the loss of every `u` on the centred dense problem, read in `ℝ` — whatever solver produced
`θ`, at any `λ > 0`. -/
theorem checkResidual_sound {θ : Vec ℚ (d + 1)} {ε : ℚ} (h : S.checkResidual θ ε = true)
    (u : Vec ℝ (d + 1)) :
    (S.toProblem.map fun q : ℚ ↦ (q : ℝ)).loss (castVec θ) ≤
      (S.toProblem.map fun q : ℚ ↦ (q : ℝ)).loss u + ε :=
  S.toProblem.checkResidual_sound (S.checkResidual_eq θ ε ▸ h) u

end SparseProblem

end LeanLearn.Regression
