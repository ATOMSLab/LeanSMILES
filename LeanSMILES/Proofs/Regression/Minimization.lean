/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
import LeanSMILES.Proofs.Regression.GradientDescent
import LeanSMILES.Proofs.Regression.Iterative
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# LeanSMILES.Proofs.Regression.Minimization

Minimizers of the ridge loss, and what the solvers have to do with them.

For a problem with `λ ≥ 0`, write `A θ = b` for its normal equations and
`IsMinimizer θ` for `∀ u, L(θ) ≤ L(u)`.

* **Minimizers are the solutions of the normal equations**
  (`isMinimizer_iff_residual_eq_zero`). One direction is the exact quadratic expansion;
  for the other, a minimizer with a nonzero residual would be beaten by a short gradient
  step.
* **…and the fixed points of the solvers**: of gradient descent for any `η ≠ 0`
  (`isMinimizer_iff_gdStep_eq_self`) and of Jacobi (`isMinimizer_iff_jacobiStep_eq_self`).
  A Gauss–Seidel sweep fixes every minimizer (`gsSweep_eq_self_of_isMinimizer`). So a
  solver that has stopped moving has found the optimum, and an optimum stops every solver.
* **With a ridge penalty `λ > 0`** the loss is strongly convex:
  `λ ‖θ - θ*‖² ≤ L(θ) - L(θ*)` (`ridge_mul_dist_le`). Hence a minimizer **exists**
  (`exists_isMinimizer`: `A` is invertible) and is **unique** (`isMinimizer_unique`), and a
  parameter vector with small excess loss is close to it.
-/

namespace LeanSMILES.Regression

open Finset

namespace Problem

variable {m d : ℕ} (P : Problem ℝ m d)

/-- `θ` minimises the loss over all parameter vectors. -/
def IsMinimizer (θ : Vec ℝ (d + 1)) : Prop := ∀ u : Vec ℝ (d + 1), P.loss θ ≤ P.loss u

theorem smoothness_nonneg (hridge : 0 ≤ P.ridge) : 0 ≤ P.smoothness :=
  add_nonneg (div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
    (Nat.cast_nonneg m)) hridge

/-! ## Minimizers solve the normal equations -/

/-- A minimizer has zero residual: otherwise the step `θ - t (A θ - b)` with
`t = 1 / (Λ + 1)` would lower the loss by at least `t ‖A θ - b‖²`. -/
theorem residual_eq_zero_of_isMinimizer (hridge : 0 ≤ P.ridge) {θ : Vec ℝ (d + 1)}
    (hmin : P.IsMinimizer θ) (i : Fin (d + 1)) : (P.res θ)[i] = 0 := by
  set r := P.res θ
  set S := ∑ j : Fin (d + 1), r[j] ^ 2 with hS
  set Λ := P.smoothness
  have hΛ : 0 ≤ Λ := P.smoothness_nonneg hridge
  set t : ℝ := 1 / (Λ + 1) with ht_def
  have ht : 0 < t := by positivity
  have htΛ : t * Λ ≤ 1 := by
    rw [ht_def, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
    linarith
  have hSnn : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have h := hmin (vadd θ (smul (-t) r))
  rw [P.loss_add, P.curvature_smul] at h
  have hsum : ∑ j : Fin (d + 1), r[j] * (smul (-t) r)[j] = -t * S := by
    rw [hS, mul_sum]
    exact sum_congr rfl fun j _ => by rw [smul_getElem]; ring
  rw [hsum] at h
  have hC : P.curvature r ≤ Λ * S := P.curvature_le r
  have h1 : (-t) ^ 2 * P.curvature r ≤ t * (t * Λ * S) := by
    calc (-t) ^ 2 * P.curvature r ≤ (-t) ^ 2 * (Λ * S) :=
          mul_le_mul_of_nonneg_left hC (sq_nonneg _)
      _ = t * (t * Λ * S) := by ring
  have h2 : t * (t * Λ * S) ≤ t * S :=
    mul_le_mul_of_nonneg_left (by nlinarith) ht.le
  have htS : t * S ≤ t * 0 := by linarith
  have hS0 : S = 0 := le_antisymm (le_of_mul_le_mul_left htS ht) hSnn
  have := (sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (r[j])).mp hS0 i (mem_univ i)
  exact pow_eq_zero_iff two_ne_zero |>.mp this

/-- **Minimizers are exactly the solutions of the normal equations.** -/
theorem isMinimizer_iff_residual_eq_zero (hridge : 0 ≤ P.ridge) (θ : Vec ℝ (d + 1)) :
    P.IsMinimizer θ ↔ ∀ i : Fin (d + 1), (P.res θ)[i] = 0 :=
  ⟨fun h => P.residual_eq_zero_of_isMinimizer hridge h,
    fun h u => P.loss_le_of_residual_eq_zero hridge h u⟩

/-! ## Minimizers are the fixed points of the solvers -/

/-- **Fixed points of gradient descent** (any `η ≠ 0`) are the minimizers. -/
theorem isMinimizer_iff_gdStep_eq_self (hridge : 0 ≤ P.ridge) {η : ℝ} (hη : η ≠ 0)
    (θ : Vec ℝ (d + 1)) :
    P.IsMinimizer θ ↔ gdStep P.normalMatrix P.normalVector η θ = θ := by
  rw [P.isMinimizer_iff_residual_eq_zero hridge, gdStep_eq]
  constructor
  · intro h
    exact vext fun i => by rw [vadd_getElem, smul_getElem, h i, mul_zero, add_zero]
  · intro h i
    have := congrArg (·[i]) h
    simp only [vadd_getElem, smul_getElem, add_eq_left, mul_eq_zero, neg_eq_zero] at this
    rcases this with h2 | hr
    · exact absurd h2 (by simpa using hη)
    · exact hr

/-- `(A θ - b)ᵢ = ∑_{j≠i} Aᵢⱼ θⱼ + Aᵢᵢ θᵢ - bᵢ`. -/
theorem residual_eq_offDiag (θ : Vec ℝ (d + 1)) (i : Fin (d + 1)) :
    (P.res θ)[i] = offDiag P.normalMatrix θ i + P.normalMatrix[i][i] * θ[i] -
      P.normalVector[i] := by
  simp [residual, offDiag, matVec]

/-- At a solution of the normal equations, solving equation `i` returns `θᵢ`. -/
theorem coordSolve_eq_self (hridge : 0 ≤ P.ridge) {θ : Vec ℝ (d + 1)}
    (h : ∀ i : Fin (d + 1), (P.res θ)[i] = 0) (i : Fin (d + 1)) :
    coordSolve P.normalMatrix P.normalVector θ i = θ[i] := by
  rcases (P.normalMatrix_diag_nonneg hridge i).lt_or_eq with hA | hA
  · rw [coordSolve_of_ne hA.ne', div_eq_iff hA.ne']
    have := P.residual_eq_offDiag θ i
    rw [h i] at this
    linarith
  · exact coordSolve_of_eq hA.symm

/-- **Fixed points of Jacobi** are the minimizers. -/
theorem isMinimizer_iff_jacobiStep_eq_self (hridge : 0 ≤ P.ridge) (θ : Vec ℝ (d + 1)) :
    P.IsMinimizer θ ↔ jacobiStep P.normalMatrix P.normalVector θ = θ := by
  constructor
  · intro h
    have hr := P.residual_eq_zero_of_isMinimizer hridge h
    exact vext fun i => by rw [jacobiStep_getElem, P.coordSolve_eq_self hridge hr i]
  · exact fun hfix u => P.loss_le_of_jacobiStep_eq_self hridge hfix u

/-- A Gauss–Seidel update leaves a solution of the normal equations unchanged. -/
theorem gsUpdate_eq_self (hridge : 0 ≤ P.ridge) {θ : Vec ℝ (d + 1)}
    (h : ∀ i : Fin (d + 1), (P.res θ)[i] = 0) (i : Fin (d + 1)) :
    gsUpdate P.normalMatrix P.normalVector θ i = θ :=
  vext fun j => by
    rw [gsUpdate_getElem]
    split_ifs with hj
    · subst hj; exact P.coordSolve_eq_self hridge h j
    · rfl

/-- **A Gauss–Seidel sweep fixes every minimizer.** -/
theorem gsSweep_eq_self_of_isMinimizer (hridge : 0 ≤ P.ridge) {θ : Vec ℝ (d + 1)}
    (hmin : P.IsMinimizer θ) : gsSweep P.normalMatrix P.normalVector θ = θ := by
  have hr := P.residual_eq_zero_of_isMinimizer hridge hmin
  unfold gsSweep
  suffices ∀ l : List (Fin (d + 1)), l.foldl (gsUpdate P.normalMatrix P.normalVector) θ = θ from
    this _
  intro l
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldl_cons, P.gsUpdate_eq_self hridge hr i, ih]

/-! ## With a ridge penalty: strong convexity, existence, uniqueness -/

/-- With `λ ≥ 0`, the curvature is at least `λ ‖v‖²`. -/
theorem ridge_mul_le_curvature (v : Vec ℝ (d + 1)) :
    P.ridge * ∑ i : Fin (d + 1), v[i] ^ 2 ≤ P.curvature v := by
  rw [curvature]
  linarith [div_nonneg (sum_nonneg fun r (_ : r ∈ univ) => sq_nonneg (P.fit r v))
    (Nat.cast_nonneg (α := ℝ) m)]

/-- **Strong convexity**: for a minimizer `θ*`, `λ ‖θ - θ*‖² ≤ L(θ) - L(θ*)`. Small excess
loss means close to the optimum. -/
theorem ridge_mul_dist_le (hridge : 0 ≤ P.ridge) {θs : Vec ℝ (d + 1)}
    (hmin : P.IsMinimizer θs) (θ : Vec ℝ (d + 1)) :
    P.ridge * ∑ i : Fin (d + 1), (θ[i] - θs[i]) ^ 2 ≤ P.loss θ - P.loss θs := by
  have hr := P.residual_eq_zero_of_isMinimizer hridge hmin
  rw [P.loss_eq_of_residual_eq_zero hr θ]
  have := P.ridge_mul_le_curvature (vsub θ θs)
  simp only [vsub_getElem] at this
  linarith

/-- **The minimizer is unique** when `λ > 0`. -/
theorem isMinimizer_unique (hridge : 0 < P.ridge) {θ θ' : Vec ℝ (d + 1)}
    (h : P.IsMinimizer θ) (h' : P.IsMinimizer θ') : θ = θ' := by
  have hd := P.ridge_mul_dist_le hridge.le h θ'
  have hle := h' θ
  have h0 : ∑ i : Fin (d + 1), (θ'[i] - θ[i]) ^ 2 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have := mul_pos hridge hpos
    linarith [h θ']
  have hz := le_antisymm h0 (sum_nonneg fun _ _ => sq_nonneg _)
  exact vext fun i => by
    have := (sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (θ'[j] - θ[j])).mp hz i (mem_univ i)
    linarith [pow_eq_zero_iff two_ne_zero |>.mp this]

/-- With `λ > 0`, `A` is invertible: `A v = 0` forces `λ ‖v‖² ≤ vᵀ A v = 0`. -/
theorem det_normalMatrix_ne_zero (hridge : 0 < P.ridge) :
    (toMatrix P.normalMatrix).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  set w : Vec ℝ (d + 1) := Vector.ofFn v
  have hcurv : P.curvature w = 0 := by
    rw [curvature_eq]
    have : ∀ i : Fin (d + 1), ∑ j : Fin (d + 1), P.normalMatrix[i][j] * w[i] * w[j] =
        w[i] * (toMatrix P.normalMatrix).mulVec v i := fun i => by
      simp only [w, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Matrix.mulVec, dotProduct,
        toMatrix, Matrix.of_apply, mul_sum]
      exact sum_congr rfl fun j _ => by ring
    simp only [this, hv, Pi.zero_apply, mul_zero, sum_const_zero]
  have h := P.ridge_mul_le_curvature w
  rw [hcurv] at h
  have hz : ∑ i : Fin (d + 1), w[i] ^ 2 = 0 :=
    le_antisymm (le_of_mul_le_mul_left (by simpa using h) hridge)
      (sum_nonneg fun _ _ => sq_nonneg _)
  funext i
  have := (sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (w[j])).mp hz i (mem_univ i)
  simpa [w] using pow_eq_zero_iff two_ne_zero |>.mp this

/-- **A minimizer exists** when `λ > 0`. -/
theorem exists_isMinimizer (hridge : 0 < P.ridge) :
    ∃ θs : Vec ℝ (d + 1), P.IsMinimizer θs := by
  obtain ⟨θs, hsol⟩ := exists_solution_of_det_ne_zero (P.det_normalMatrix_ne_zero hridge)
    P.normalVector
  refine ⟨θs, (P.isMinimizer_iff_residual_eq_zero hridge.le θs).mpr fun i => ?_⟩
  change (residual P.normalMatrix P.normalVector θs)[i] = 0
  rw [residual, vsub_getElem, hsol i, sub_self]

/-- Under weighted diagonal dominance (any `λ ≥ 0`), the normal equations have a solution
and it is a minimizer. -/
theorem exists_isMinimizer_of_diagDominant (hridge : 0 ≤ P.ridge) {w : Vec ℝ (d + 1)} {ρ : ℝ}
    (hdd : DiagDominant P.normalMatrix w ρ) :
    ∃ θs : Vec ℝ (d + 1),
      (∀ i : Fin (d + 1), (matVec P.normalMatrix θs)[i] = P.normalVector[i]) ∧
        P.IsMinimizer θs := by
  obtain ⟨θs, hsol⟩ := exists_solution hdd P.normalVector
  refine ⟨θs, hsol, (P.isMinimizer_iff_residual_eq_zero hridge θs).mpr fun i => ?_⟩
  change (residual P.normalMatrix P.normalVector θs)[i] = 0
  rw [residual, vsub_getElem, hsol i, sub_self]

end Problem

end LeanSMILES.Regression
