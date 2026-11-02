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
  `Proofs/Regression/Basic.lean`, which holds over any field, at the exact arithmetic the
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

/-! ## The dense residual, entrywise, over `ℚ` -/

namespace Problem

variable {m d : ℕ} (P : Problem ℚ m d)

/-- The exact residual of the normal equations at `θ`, entrywise:
`(A θ − b)ᵢ = (1/m) Σᵣ xᵣᵢ (⟪xᵣ, θ⟫ − yᵣ) + λ θᵢ` — `residual_apply` at `ℚ`. -/
theorem residualAt_apply (θ : Vec ℚ (d + 1)) (i : Fin (d + 1)) : (P.residualAt θ)[i] =
    (∑ r : Fin m, (P.row r)[i] * (dot (P.row r) θ - P.y[r])) / m + P.ridge * θ[i] :=
  P.residual_apply θ i

end Problem

/-! ## The sparse computations are the dense ones -/

namespace SparseProblem

variable {m d : ℕ}

/-- Entry `i` of `addAt acc c l` gains `c` once per occurrence of `i` in `l`. -/
theorem addAt_getElem (acc : Vec ℚ d) (c : ℚ) (l : List (Fin d)) (i : Fin d) :
    (addAt acc c l)[i] = acc[i] + (l.count i : ℚ) * c := by
  induction l generalizing acc with
  | nil => simp [addAt]
  | cons j l ih =>
    rw [addAt, List.foldl_cons, ← addAt, ih, List.count_cons]
    push_cast
    grind

-- Scatter-add over any list of rows, from any accumulator: `scatter_getElem` before the
-- rows are `List.finRange m` and the accumulator is `vzero`.
private theorem foldl_addAt_getElem (bits : Vector (List (Fin d)) m) (v : Vec ℚ m) (i : Fin d)
    (rs : List (Fin m)) (acc : Vec ℚ d) :
    (rs.foldl (fun acc r ↦ addAt acc v[r] bits[r]) acc)[i] =
      acc[i] + (rs.map fun r ↦ (bits[r].count i : ℚ) * v[r]).sum := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih, addAt_getElem, List.map_cons, List.sum_cons, add_assoc]

/-- Scatter-add over the rows is `Xᵀ v`. -/
theorem scatter_getElem (bits : Vector (List (Fin d)) m) (v : Vec ℚ m) (i : Fin d) :
    (scatter bits v)[i] = ∑ r : Fin m, (bits[r].count i : ℚ) * v[r] := by
  rw [scatter, foldl_addAt_getElem, Fin.sum_univ_def]
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
    simp [List.count_cons, add_mul, sum_add_distrib, add_comm]

variable (S : SparseProblem m d)

/-- The dense problem keeps the sparse ridge penalty `λ`. -/
@[simp] theorem toProblem_ridge : S.toProblem.ridge = S.ridge := rfl

/-- The dense targets are the sparse ones centred on their mean `ȳ`. -/
theorem toProblem_y (r : Fin m) : S.toProblem.y[r] = S.y[r] - S.yMean := by
  simp [toProblem]

/-- The bit mean `x̄ⱼ` is the count of bit `j`, averaged over the rows. -/
theorem means_getElem (j : Fin d) : S.means[j] = (∑ r : Fin m, (S.bits[r].count j : ℚ)) / m := by
  simp [means]

/-- Feature `j` of dense row `r` is the count of bit `j` in row `r`, centred on its mean. -/
theorem row_castSucc (r : Fin m) (j : Fin d) :
    (S.toProblem.row r)[j.castSucc] = (S.bits[r].count j : ℚ) - S.means[j] := by
  simp [Problem.row, augment, toProblem]

/-- The last entry of every dense row is the constant feature `1`. -/
theorem row_last (r : Fin m) : (S.toProblem.row r)[Fin.last d] = 1 := by
  simp [Problem.row, augment, toProblem]

/-! The same with natural-number indices. -/

/-- `row_castSucc` at a natural-number index, the form `simp` normalises to. -/
theorem row_castSucc' (r : Fin m) (j : Fin d) :
    (S.toProblem.row r)[(j : ℕ)] = (S.bits[r].count j : ℚ) - S.means[j] :=
  S.row_castSucc r j

/-- `row_last` at the natural-number index `d`, the form `simp` normalises to. -/
theorem row_last' (r : Fin m) : (S.toProblem.row r)[d] = 1 := S.row_last r

/-- The dense fitted value `⟪xᵣ, θ⟫`, split into the centred bit counts and the bias. -/
theorem fitted_eq (θ : Vec ℚ (d + 1)) (r : Fin m) : dot (S.toProblem.row r) θ =
    ∑ j : Fin d, ((S.bits[r].count j : ℚ) - S.means[j]) * θ[j.castSucc] + θ[Fin.last d] := by
  simp only [dot_eq_sum, Fin.sum_univ_castSucc, row_castSucc, row_last, one_mul]

/-- The sparse errors are the dense ones: `⟪xᵣ, θ⟫ − yᵣ` on the centred problem. -/
theorem errors_getElem (θ : Vec ℚ (d + 1)) (r : Fin m) :
    (S.errors θ)[r] = dot (S.toProblem.row r) θ - S.toProblem.y[r] := by
  rw [fitted_eq, toProblem_y]
  simp [errors, sumGen_count, sumFin_eq_sum, sub_mul]

/-- **The sparse residual is the dense residual.** -/
theorem residual_eq (θ : Vec ℚ (d + 1)) : S.residual θ = S.toProblem.residualAt θ := by
  refine vext fun i ↦ ?_
  simp only [Problem.residualAt_apply, ← errors_getElem]
  induction i using Fin.lastCases <;>
    simp [residual, row_last', row_castSucc', sumFin_eq_sum, sub_mul, mul_sum]

/-- The sparse loss is the dense loss. -/
theorem loss_eq (θ : Vec ℚ (d + 1)) : S.loss θ = S.toProblem.loss θ := by
  simp only [loss, Problem.loss, errors_getElem, toProblem_ridge, count_eq_natCast]

/-- The sparse certified excess `‖A θ − b‖² / λ` is the dense one. -/
theorem residualExcess_eq (θ : Vec ℚ (d + 1)) :
    S.residualExcess θ = S.toProblem.residualExcess θ := by
  simp only [residualExcess, Problem.residualExcess, residual_eq, toProblem_ridge]

/-- The sparse check is the dense check. -/
theorem checkResidual_eq (θ : Vec ℚ (d + 1)) (ε : ℚ) :
    S.checkResidual θ ε = S.toProblem.checkResidual θ ε := by
  rw [checkResidual, residual_eq]
  rfl

/-- **Soundness of the sparse residual check**: if it passes, the cast of `θ` is within `ε`
of the loss of every `u` on the centred dense problem, read in `ℝ` — whatever solver produced
`θ`, at any `λ > 0`. -/
theorem checkResidual_sound {θ : Vec ℚ (d + 1)} {ε : ℚ} (h : S.checkResidual θ ε = true)
    (u : Vec ℝ (d + 1)) : (S.toProblem.map fun q : ℚ ↦ (q : ℝ)).loss (castVec θ) ≤
      (S.toProblem.map fun q : ℚ ↦ (q : ℝ)).loss u + ε :=
  S.toProblem.checkResidual_sound (S.checkResidual_eq θ ε ▸ h) u

end SparseProblem

end LeanLearn.Regression
