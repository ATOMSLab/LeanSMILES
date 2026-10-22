/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import LeanLearn.Scalar
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# The linear model on a Mathlib matrix, over any scalar

The prediction `Xw`, the residual `Xw − y`, the squared error `‖Xw − y‖²`, the diagonal
penalty `Σⱼ ρⱼ wⱼ²` and the ridge objective, written with `sumFin` over `PolynomialLike`
(`LeanLearn/Scalar.lean`) so that they run at `Float` and read exactly at `ℚ` and `ℝ`. The
design is a Mathlib `Matrix (Fin n) (Fin p) K`; the caller supplies any intercept column.

`Proofs/Regression/LinearModel.lean` proves that at `ℝ` these are the closed-form
specifications of `Proofs/LeastSquares/OLS.lean` and `Ridge.lean`, so the optimality theorems
there apply to the executable objectives. No lawful ring instance or optimality theorem is
asserted at `Float`.
-/

@[expose] public section

namespace LeanLearn.Regression.LinearModel

variable {K : Type} {n p : ℕ} [PolynomialLike K]

/-- Dimension-safe feature rows. The caller supplies any intercept column explicitly. -/
abbrev Design (K : Type) (n p : ℕ) := Matrix (Fin n) (Fin p) K

/-- One coefficient per supplied feature. -/
abbrev Coefficients (K : Type) (p : ℕ) := Fin p → K

/-- Prediction for one feature vector, including a supplied intercept feature. -/
def predictRow (x w : Fin p → K) : K := sumFin fun j ↦ x j * w j

/-- Predicted targets on a supplied numerical design. -/
def predict (X : Design K n p) (w : Coefficients K p) : Fin n → K :=
  fun i ↦ predictRow (X i) w

/-- Prediction minus observed target. -/
def residual (X : Design K n p) (y : Fin n → K) (w : Coefficients K p) : Fin n → K :=
  fun i ↦ predict X w i - y i

/-- OLS objective, a sum of squared residuals without averaging. -/
def squaredError (X : Design K n p) (y : Fin n → K) (w : Coefficients K p) : K :=
  sumFin fun i ↦ let r := residual X y w i; r * r

/-- Diagonal coefficient penalty. A zero weight exempts that coefficient. -/
def penalty (weights w : Fin p → K) : K := sumFin fun j ↦ weights j * (w j * w j)

/-- Ridge objective; constant weights give standard ridge. -/
def ridgeLoss (X : Design K n p) (y : Fin n → K) (weights w : Fin p → K) : K :=
  squaredError X y w + penalty weights w

/-- Half the exact-real objective gradient, expressed with Float-compatible operations. -/
def normalResidual (X : Design K n p) (y : Fin n → K)
    (weights w : Fin p → K) : Fin p → K :=
  fun j ↦ (sumFin fun i ↦ X i j * residual X y w i) + weights j * w j

end LeanLearn.Regression.LinearModel
