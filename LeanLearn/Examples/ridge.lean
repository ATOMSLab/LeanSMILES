/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import LeanLearn.Proofs.LeastSquares.RidgeOLS
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Kernel-checked ridge examples over exact real numbers -/

public section

namespace LeanLearn.Regression.Ridge.Examples

open Matrix
open scoped Matrix

noncomputable section

/-- Inputs `x = 0, 1, 2` behind an intercept column of ones: the design of the OLS examples. -/
def lineX : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 1, 1; 1, 2]

/-- Targets lying exactly on `y = 1 + 2x`, which OLS therefore fits with zero error. -/
def lineY : Fin 3 → ℝ := ![1, 3, 5]

/-- An explicit intercept is exempt from the slope penalty of 2. -/
theorem exempt_normalEquations : NormalEquations lineX lineY ![0, 2] ![2, 1] := by
  unfold NormalEquations
  ext j
  fin_cases j <;> norm_num [gram, OLS.gram, lineX, lineY, mulVec, mul_apply, dotProduct,
    Fin.sum_univ_succ, diagonal]

/-- With the intercept exempt, `![2, 1]` globally minimizes the ridge loss on the line data. -/
theorem exempt_minimizes : IsMinimizer lineX lineY ![0, 2] ![2, 1] :=
  normalEquations_minimize lineX lineY (by simp) exempt_normalEquations

/-- The minimal ridge loss on the line data: squared error `2` plus penalty `2 · 1²`. -/
theorem exempt_loss : loss lineX lineY ![0, 2] ![2, 1] = 4 := by
  norm_num [loss_eq_sum, OLS.predict, lineX, lineY, mulVec, dotProduct, Fin.sum_univ_succ]

/-- A lower bound on the objective for every real intercept and slope. -/
theorem exempt_lower_bound (w : Fin 2 → ℝ) : 4 ≤ loss lineX lineY ![0, 2] w :=
  exempt_loss ▸ exempt_minimizes w

/-- Two identical feature columns: a design on which OLS cannot identify the coefficients. -/
def duplicateX : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]

/-- Two different targets observed at the same repeated input. -/
def duplicateY : Fin 2 → ℝ := ![1, 3]

/-- Ridge identifies both coefficients even when feature columns are identical. -/
theorem duplicate_normalEquations :
    NormalEquations duplicateX duplicateY (fun _ ↦ 1) ![4 / 5, 4 / 5] := by
  unfold NormalEquations
  ext j
  fin_cases j <;> norm_num [gram, OLS.gram, duplicateX, duplicateY, mulVec, mul_apply,
    dotProduct, Fin.sum_univ_succ, diagonal]

/-- The closed form needs no rank condition: on the duplicate-column data it returns
`![4 / 5, 4 / 5]`, the normal-equations solution, because the minimizer is unique. -/
theorem duplicate_fit :
    fitPositive duplicateX duplicateY (fun _ ↦ 1) (fun _ ↦ one_pos) = ![4 / 5, 4 / 5] :=
  -- a normal-equations solution is a minimizer, and `fitPositive` is the unique one
  (fitPositive_unique _ _ _ _ (normalEquations_minimize _ _ (fun _ ↦ zero_le_one)
    duplicate_normalEquations)).symm

/-- One observation and two coefficients: positive ridge still has a unique solution. -/
theorem underdetermined_minimizes : IsMinimizer !![1, 2] ![3] (fun _ ↦ 1) ![1 / 2, 1] := by
  refine normalEquations_minimize _ _ (fun _ ↦ zero_le_one) ?_
  unfold NormalEquations
  ext j
  fin_cases j <;> norm_num [gram, OLS.gram, mulVec, mul_apply, dotProduct, Fin.sum_univ_succ,
    diagonal]

/-! ## Ridge against OLS on the same data -/

/-- Without a penalty, the line `y = 1 + 2x` fits `lineX`, `lineY` exactly. -/
theorem ols_normalEquations : OLS.NormalEquations lineX lineY ![1, 2] := by
  rw [OLS.normalEquations_iff]
  ext j
  fin_cases j <;> norm_num [OLS.gram, lineX, lineY, mulVec, mul_apply, dotProduct,
    Fin.sum_univ_succ]

/-- The trade-off, by theorem rather than by computation: the exempt-intercept ridge fit
`![2, 1]` has a smaller penalized norm than the OLS fit `![1, 2]`. -/
theorem exempt_penalty_le : penalty ![0, 2] ![2, 1] ≤ penalty ![0, 2] ![1, 2] :=
  penalty_le_of_isMinimizer lineX lineY (OLS.normalEquations_minimize _ _ ols_normalEquations)
    exempt_minimizes

/-- The numbers behind `exempt_penalty_le`: penalties `2 ≤ 8`, bought by giving up squared
error `0 ≤ 2`. -/
theorem exempt_tradeoff : penalty ![0, 2] ![2, 1] = 2 ∧ penalty ![0, 2] ![1, 2] = 8 ∧
    OLS.loss lineX lineY ![1, 2] = 0 ∧ OLS.loss lineX lineY ![2, 1] = 2 := by
  norm_num [penalty, OLS.loss_eq_sum, OLS.predict, lineX, lineY, mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- A `3 × 2` design with orthonormal columns, so `XᵀX = 1` and ridge merely rescales OLS. -/
def orthoX : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

/-- `orthoX` has Gram matrix `1`, the hypothesis of `fitPositive_eq_smul_of_gram_eq_one`. -/
theorem orthoX_gram : OLS.gram orthoX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [OLS.gram, orthoX, mul_apply, one_apply,
    Fin.sum_univ_succ]

/-- The transpose of `orthoX` as a literal, so that `Xᵀy` can be evaluated entrywise. -/
theorem orthoX_transpose : orthoXᵀ = !![1, 0, 0; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- With orthonormal columns, unit ridge halves the OLS coefficients `Xᵀy = ![2, 4]`. -/
theorem ortho_halves : fitPositive orthoX ![2, 4, 6] (fun _ ↦ 1) (fun _ ↦ one_pos) = ![1, 2] := by
  rw [fitPositive_eq_smul_of_gram_eq_one orthoX _ orthoX_gram one_pos, orthoX_transpose]
  ext j
  fin_cases j <;> norm_num [mulVec, dotProduct, Fin.sum_univ_succ]

end

end LeanLearn.Regression.Ridge.Examples
