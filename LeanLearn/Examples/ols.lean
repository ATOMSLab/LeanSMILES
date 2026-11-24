/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import LeanLearn.Proofs.LeastSquares.OLS
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Small, exact examples of the OLS theorems

These examples are checked proofs over `ℝ`, not numerical training experiments.
The first column of each design matrix is the intercept column.
-/

public section

namespace LeanLearn.Regression.OLS.Examples

open Matrix
open scoped Matrix

noncomputable section

/-- Three inputs `x = 0, 1, 2`, augmented by an intercept column of ones. -/
def lineDesign : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 1, 1; 1, 2]

/-- Targets lying exactly on `y = 1 + 2x`. -/
def lineTargets : Fin 3 → ℝ := ![1, 3, 5]

/-- The coefficients of `y = 1 + 2x`: intercept first, then slope. -/
def lineCoefficients : Fin 2 → ℝ := ![1, 2]

/-- The Gram determinant is nonzero, so the closed-form algorithm is applicable. -/
theorem line_nonsingular : (gram lineDesign).det ≠ 0 := by
  norm_num [gram, lineDesign, det_fin_two, mul_apply, Fin.sum_univ_succ]

/-- The exact line satisfies the normal equations `XᵀXw = Xᵀy`. -/
theorem line_normalEquations : NormalEquations lineDesign lineTargets lineCoefficients := by
  rw [normalEquations_iff]
  -- both coordinates of `XᵀXw = Xᵀy` are checked by direct computation
  ext j
  fin_cases j <;> norm_num [gram, lineDesign, lineTargets, lineCoefficients, mulVec, mul_apply,
    dotProduct, Fin.sum_univ_succ]

/-- The closed-form algorithm returns intercept `1` and slope `2`. -/
theorem line_fit : fit lineDesign lineTargets line_nonsingular = lineCoefficients :=
  -- a normal-equations solution is a minimizer, and `fit` is the unique minimizer
  (fit_unique _ _ _ (normalEquations_minimize _ _ line_normalEquations)).symm

/-- This line fits every observation exactly. -/
theorem line_loss_zero : loss lineDesign lineTargets lineCoefficients = 0 := by
  norm_num [loss_eq_sum, predict, lineDesign, lineTargets, lineCoefficients, mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- Targets `1, 2, 4` at the inputs of `lineDesign`; no single line passes through all three. -/
def noisyTargets : Fin 3 → ℝ := ![1, 2, 4]

/-- The best-fit line has intercept `5/6` and slope `3/2`. -/
def noisyCoefficients : Fin 2 → ℝ := ![5 / 6, 3 / 2]

/-- Even though the residual is nonzero, it is orthogonal to the feature columns. -/
theorem noisy_normalEquations : NormalEquations lineDesign noisyTargets noisyCoefficients := by
  rw [normalEquations_iff]
  ext j
  fin_cases j <;> norm_num [gram, lineDesign, noisyTargets, noisyCoefficients, mulVec, mul_apply,
    dotProduct, Fin.sum_univ_succ]

/-- The best-fit line misses the noisy targets by a total squared error of exactly `1/6`. -/
theorem noisy_loss : loss lineDesign noisyTargets noisyCoefficients = 1 / 6 := by
  norm_num [loss_eq_sum, predict, lineDesign, noisyTargets, noisyCoefficients, mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- Every intercept/slope pair has squared error at least `1/6` on the noisy data. -/
theorem noisy_loss_lower_bound (w : Fin 2 → ℝ) : 1 / 6 ≤ loss lineDesign noisyTargets w :=
  noisy_loss ▸ normalEquations_minimize lineDesign noisyTargets noisy_normalEquations w

/-- The closed-form algorithm returns the proved best-fit coefficients on noisy data. -/
theorem noisy_fit : fit lineDesign noisyTargets line_nonsingular = noisyCoefficients :=
  (fit_unique _ _ _ (normalEquations_minimize _ _ noisy_normalEquations)).symm

/-- Two identical feature columns: coefficients cannot be uniquely identified. -/
def singularDesign : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]

/-- The repeated inputs have two different observed targets. -/
def singularTargets : Fin 2 → ℝ := ![1, 3]

/-- The nonsingularity hypothesis required by `fit` genuinely fails in this example. -/
theorem singular_gram_det : (gram singularDesign).det = 0 := by
  norm_num [gram, singularDesign, det_fin_two, mul_apply]

/-- A singular design can have different coefficient vectors that both minimize loss, so
`fit_unique` genuinely needs its nonsingularity hypothesis. -/
theorem singular_two_minimizers : IsMinimizer singularDesign singularTargets ![2, 0] ∧
    IsMinimizer singularDesign singularTargets ![0, 2] ∧ (![2, 0] : Fin 2 → ℝ) ≠ ![0, 2] := by
  refine ⟨normalEquations_minimize _ _ ?_, normalEquations_minimize _ _ ?_, by simp⟩
  -- both candidates satisfy the normal equations, checked coordinate by coordinate
  all_goals
    rw [normalEquations_iff]
    ext j
    fin_cases j <;> norm_num [gram, singularDesign, singularTargets, mulVec, mul_apply, dotProduct,
      Fin.sum_univ_succ]

end

end LeanLearn.Regression.OLS.Examples
