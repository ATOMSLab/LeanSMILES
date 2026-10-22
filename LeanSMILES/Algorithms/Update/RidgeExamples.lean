import LeanSMILES.Algorithms.Update.Ridge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Kernel-checked ridge examples over exact real numbers -/
namespace LeanSMILES.Algorithms.Update.Ridge.Examples
open Matrix
open scoped Matrix BigOperators
noncomputable section

def lineX : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 1, 1; 1, 2]
def lineY : Fin 3 → ℝ := ![1, 3, 5]

/-- An explicit intercept is exempt from the slope penalty of 2. -/
theorem exempt_normalEquations : NormalEquations lineX lineY ![0, 2] ![2, 1] := by
  unfold NormalEquations
  ext j
  fin_cases j <;> norm_num [gram, OLS.gram, lineX, lineY, Matrix.mulVec,
    Matrix.mul_apply, dotProduct, Fin.sum_univ_succ, diagonal]

theorem exempt_minimizes : IsMinimizer lineX lineY ![0, 2] ![2, 1] := by
  apply normalEquations_minimize lineX lineY _ exempt_normalEquations
  intro j
  fin_cases j <;> norm_num

theorem exempt_loss : loss lineX lineY ![0, 2] ![2, 1] = 4 := by
  norm_num [loss_eq_sum, OLS.predict, lineX, lineY, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- A lower bound on the objective for every real intercept and slope. -/
theorem exempt_lower_bound (w : Fin 2 → ℝ) : 4 ≤ loss lineX lineY ![0, 2] w := by
  have h := exempt_minimizes w
  rwa [exempt_loss] at h

def duplicateX : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]
def duplicateY : Fin 2 → ℝ := ![1, 3]

/-- Ridge identifies both coefficients even when feature columns are identical. -/
theorem duplicate_normalEquations :
    NormalEquations duplicateX duplicateY (fun _ => 1) ![4/5, 4/5] := by
  unfold NormalEquations
  ext j
  fin_cases j <;> norm_num [gram, OLS.gram, duplicateX, duplicateY, Matrix.mulVec,
    Matrix.mul_apply, dotProduct, Fin.sum_univ_succ, diagonal]

theorem duplicate_fit : fitPositive duplicateX duplicateY (fun _ => 1) (by intro j; norm_num) =
    ![4/5, 4/5] := by
  symm
  apply fitPositive_unique
  apply normalEquations_minimize duplicateX duplicateY (by intro j; norm_num)
  exact duplicate_normalEquations

/-- One observation and two coefficients: positive ridge still has a unique solution. -/
theorem underdetermined_minimizes :
    IsMinimizer (!![1, 2] : Matrix (Fin 1) (Fin 2) ℝ) ![3] (fun _ => 1) ![1/2, 1] := by
  apply normalEquations_minimize _ _ (by intro j; norm_num)
  unfold NormalEquations
  ext j
  fin_cases j <;> norm_num [gram, OLS.gram, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_succ, diagonal]

end
end LeanSMILES.Algorithms.Update.Ridge.Examples
