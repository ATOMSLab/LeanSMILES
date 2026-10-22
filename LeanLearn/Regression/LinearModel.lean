module

public import LeanLearn.Scalar
public import LeanLearn.Regression.Ridge

/-!
# Scalar-polymorphic linear model and its exact-real interpretation

The feature matrix and targets are the boundary with the rest of LeanSMILES.
These definitions require no molecule, fingerprint, or dataset-splitting code.
They use the same `PolynomialLike` interface as the `canonical-smiles` branch:
the definitions execute at `Float` and their `ℝ` interpretation is proved here.
No lawful ring instance or exact optimality theorem is asserted for `Float`.
-/

@[expose] public section

namespace LeanLearn.Regression.LinearModel

open Matrix
open scoped BigOperators
variable {K : Type} {n p : ℕ}

/-- Dimension-safe feature rows. The caller supplies any intercept column explicitly. -/
abbrev Design (K : Type) (n p : ℕ) := Matrix (Fin n) (Fin p) K

/-- One coefficient per supplied feature. -/
abbrev Coefficients (K : Type) (p : ℕ) := Fin p → K

section Executable
variable [PolynomialLike K]

/-- Finite sum in a fixed order, executable even without associative Float addition. -/
def sumFin (f : Fin n → K) : K := sumGen (List.finRange n) f

/-- Prediction for one feature vector, including a supplied intercept feature. -/
def predictRow (x w : Fin p → K) : K := sumFin fun j => x j * w j

/-- Predicted targets on a supplied numerical design. -/
def predict (X : Design K n p) (w : Coefficients K p) : Fin n → K :=
  fun i => predictRow (X i) w

/-- Prediction minus observed target. -/
def residual (X : Design K n p) (y : Fin n → K) (w : Coefficients K p) : Fin n → K :=
  fun i => predict X w i - y i

/-- OLS objective, a sum of squared residuals without averaging. -/
def squaredError (X : Design K n p) (y : Fin n → K) (w : Coefficients K p) : K :=
  sumFin fun i => let r := residual X y w i; r * r

/-- Diagonal coefficient penalty. A zero weight exempts that coefficient. -/
def penalty (weights w : Fin p → K) : K := sumFin fun j => weights j * (w j * w j)

/-- Ridge objective; constant weights give standard ridge. -/
def ridgeLoss (X : Design K n p) (y : Fin n → K) (weights w : Fin p → K) : K :=
  squaredError X y w + penalty weights w

/-- Half the exact-real objective gradient, expressed with Float-compatible operations. -/
def normalResidual (X : Design K n p) (y : Fin n → K)
    (weights w : Fin p → K) : Fin p → K :=
  fun j => (sumFin fun i => X i j * residual X y w i) + weights j * w j

end Executable

section RealProofs

/-- The fixed-order executable sum agrees with the mathematical finite sum at `ℝ`. -/
theorem sumFin_real (f : Fin n → ℝ) : sumFin f = ∑ i, f i := by
  rw [sumFin, sumGen_eq, ← List.sum_toFinset f (List.nodup_finRange n)]
  simp

theorem predictRow_real (x w : Fin p → ℝ) : predictRow x w = x ⬝ᵥ w := by
  simp [predictRow, sumFin_real, dotProduct]

theorem predict_real (X : Design ℝ n p) (w : Fin p → ℝ) :
    predict X w = OLS.predict X w := by
  ext i
  exact predictRow_real (X i) w

theorem residual_real (X : Design ℝ n p) (y : Fin n → ℝ) (w : Fin p → ℝ) :
    residual X y w = OLS.residual X y w := by
  ext i
  simp [residual, predict_real, OLS.residual]

/-- The Float-usable OLS definition specializes to the formally verified real objective. -/
theorem squaredError_real (X : Design ℝ n p) (y : Fin n → ℝ) (w : Fin p → ℝ) :
    squaredError X y w = OLS.loss X y w := by
  simp [squaredError, sumFin_real, residual_real, OLS.loss, dotProduct]

theorem penalty_real (weights w : Fin p → ℝ) : penalty weights w = Ridge.penalty weights w := by
  simp [penalty, sumFin_real, Ridge.penalty, pow_two]

/-- The Float-usable ridge definition specializes to the formally verified real objective. -/
theorem ridgeLoss_real (X : Design ℝ n p) (y : Fin n → ℝ) (weights w : Fin p → ℝ) :
    ridgeLoss X y weights w = Ridge.loss X y weights w := by
  rw [ridgeLoss, squaredError_real, penalty_real, Ridge.loss]

/-- Stationarity in the shared definition is exactly the real ridge normal equations. -/
theorem normalResidual_eq_zero_iff (X : Design ℝ n p) (y : Fin n → ℝ)
    (weights w : Fin p → ℝ) :
    normalResidual X y weights w = 0 ↔ Ridge.NormalEquations X y weights w := by
  rw [Ridge.normalEquations_iff]
  have h : normalResidual X y weights w =
      Xᵀ *ᵥ OLS.residual X y w + diagonal weights *ᵥ w := by
    ext j
    simp only [normalResidual, sumFin_real, residual_real, Pi.add_apply, mulVec_diagonal]
    rfl
  rw [h]

/-- Correctness of OLS expressed using the shared, executable objective definition. -/
theorem ols_fit_minimizes (X : Design ℝ n p) (y : Fin n → ℝ)
    (h : (OLS.gram X).det ≠ 0) (v : Fin p → ℝ) :
    squaredError X y (OLS.fit X y h) ≤ squaredError X y v := by
  simpa only [squaredError_real] using OLS.fit_minimizes X y h v

/-- Nonnegative diagonal ridge weights turn stationarity into global optimality. -/
theorem stationary_minimizes (X : Design ℝ n p) (y : Fin n → ℝ)
    {weights w : Fin p → ℝ} (hweights : ∀ j, 0 ≤ weights j)
    (h : normalResidual X y weights w = 0) (v : Fin p → ℝ) :
    ridgeLoss X y weights w ≤ ridgeLoss X y weights v := by
  simpa only [ridgeLoss_real] using Ridge.normalEquations_minimize X y hweights
    ((normalResidual_eq_zero_iff X y weights w).mp h) v

/-- Positive ridge's exact fit minimizes the shared ridge objective on every real design. -/
theorem ridge_fit_minimizes (X : Design ℝ n p) (y : Fin n → ℝ)
    (weights : Fin p → ℝ) (hweights : ∀ j, 0 < weights j) (v : Fin p → ℝ) :
    ridgeLoss X y weights (Ridge.fitPositive X y weights hweights) ≤
      ridgeLoss X y weights v := by
  simpa only [ridgeLoss_real] using Ridge.fitPositive_minimizes X y weights hweights v

end RealProofs
end LeanLearn.Regression.LinearModel
