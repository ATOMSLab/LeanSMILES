/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
import LeanSMILES.Regression.Basic

/-!
# Linear regression — iterative solvers

Three iterative methods for the normal equations `A θ = b` of `Basic.lean`, each started
from `θ = 0`:

* **Gradient descent**: `θ ← θ - η ∇L(θ) = θ - 2η (A θ - b)`.
* **Jacobi iteration**: every coordinate solves its own equation from the previous
  iterate, `θᵢ ← (bᵢ - ∑_{j≠i} Aᵢⱼ θⱼ) / Aᵢᵢ`.
* **Gauss–Seidel iteration**: the same, one coordinate at a time, in order, each using
  the coordinates already updated in this sweep. On the normal equations this is exact
  coordinate descent on the loss.

`Algorithm` is the choice of method with its hyperparameters, as data, so that a pipeline
can be certified by casing on it (`Proofs/Pipeline/Certificates.lean`). Hyperparameters are
exact rationals, read in the scalar type through `RatEmbed`.

What is proved (over `ℝ`, `Proofs/Regression/`): gradient descent reaches the `O(1/k)` rate
under a step-size condition; Jacobi and Gauss–Seidel converge linearly, with an explicit
excess-loss bound, when `A` is diagonally dominant with respect to some positive weights;
Gauss–Seidel never increases the loss; a fixed point of Jacobi solves the normal
equations.
-/

namespace LeanSMILES.Regression

variable {K : Type} [PolynomialLike K] [Div K] {n : ℕ}

/-- The residual `A θ - b` of the normal equations (half the loss gradient). -/
def residual (A : Mat K n n) (b θ : Vec K n) : Vec K n := vsub (matVec A θ) b

/-- `∑_{j≠i} Aᵢⱼ θⱼ`. -/
def offDiag (A : Mat K n n) (θ : Vec K n) (i : Fin n) : K := dot A[i] θ - A[i][i] * θ[i]

/-- Solve equation `i` for coordinate `i`: `(bᵢ - ∑_{j≠i} Aᵢⱼ θⱼ) / Aᵢᵢ`. If `Aᵢᵢ = 0`,
keep `θᵢ`: on the normal equations that coordinate then does not enter the loss
(`residual_eq_zero_of_diag_eq_zero`), and dividing would give `NaN` on `Float`. -/
def coordSolve [BEq K] (A : Mat K n n) (b θ : Vec K n) (i : Fin n) : K :=
  if A[i][i] == 0 then θ[i] else (b[i] - offDiag A θ i) / A[i][i]

/-! ## Gradient descent -/

/-- One gradient step `θ - 2η (A θ - b)`. -/
def gdStep (A : Mat K n n) (b : Vec K n) (η : K) (θ : Vec K n) : Vec K n :=
  let r := residual A b θ
  Vector.ofFn fun i => θ[i] - (η + η) * r[i]

/-- `k` gradient steps from `θ = 0`. -/
def gradientDescent (A : Mat K n n) (b : Vec K n) (η : K) (k : ℕ) : Vec K n :=
  (gdStep A b η)^[k] vzero

/-! ## Jacobi iteration -/

/-- One Jacobi step: `θᵢ ← (bᵢ - ∑_{j≠i} Aᵢⱼ θⱼ) / Aᵢᵢ` for every `i` at once. -/
def jacobiStep [BEq K] (A : Mat K n n) (b θ : Vec K n) : Vec K n :=
  Vector.ofFn fun i => coordSolve A b θ i

/-- `k` Jacobi steps from `θ = 0`. -/
def jacobi [BEq K] (A : Mat K n n) (b : Vec K n) (k : ℕ) : Vec K n :=
  (jacobiStep A b)^[k] vzero

/-! ## Gauss–Seidel iteration -/

/-- Solve equation `i` for coordinate `i`, keeping the others. -/
def gsUpdate [BEq K] (A : Mat K n n) (b θ : Vec K n) (i : Fin n) : Vec K n :=
  θ.set i (coordSolve A b θ i) i.isLt

/-- One Gauss–Seidel sweep: `gsUpdate` for `i = 0, 1, …, n - 1`, in place. -/
def gsSweep [BEq K] (A : Mat K n n) (b θ : Vec K n) : Vec K n :=
  (List.finRange n).foldl (gsUpdate A b) θ

/-- `k` Gauss–Seidel sweeps from `θ = 0`. -/
def gaussSeidel [BEq K] (A : Mat K n n) (b : Vec K n) (k : ℕ) : Vec K n :=
  (gsSweep A b)^[k] vzero

/-! ## The algorithm as data -/

/-- An iterative solver for linear regression, with its hyperparameters. -/
inductive Algorithm where
  /-- Gradient descent with step size `η` for `iters` steps. -/
  | gradientDescent (stepSize : ℚ) (iters : ℕ)
  /-- Jacobi iteration for `iters` steps. -/
  | jacobi (iters : ℕ)
  /-- Gauss–Seidel iteration for `sweeps` sweeps. -/
  | gaussSeidel (sweeps : ℕ)
  deriving Repr, DecidableEq

/-- Run the algorithm on the normal equations `A θ = b`. -/
def Algorithm.solve [BEq K] [RatEmbed K] : Algorithm → Mat K n n → Vec K n → Vec K n
  | .gradientDescent η k, A, b => Regression.gradientDescent A b (RatEmbed.ofRat η) k
  | .jacobi k, A, b => Regression.jacobi A b k
  | .gaussSeidel k, A, b => Regression.gaussSeidel A b k

/-- Fit the problem: run the algorithm on its normal equations. -/
def Algorithm.fit [BEq K] [RatEmbed K] {m d : ℕ} (alg : Algorithm) (P : Problem K m d) :
    Vec K (d + 1) :=
  alg.solve P.normalMatrix P.normalVector

end LeanSMILES.Regression
