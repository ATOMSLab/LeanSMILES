/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
-/
module

public import Pipelines.Pipeline
public import LeanLearn.Regression.Certificates

/-!
# Pipelines.Certificates

Certificate checks for a pipeline.

Exact `ℚ` computations that decide whether a pipeline can be certified, before training.
Each check returns a `Bool`; its soundness theorem in `Pipelines/Proofs/Certificates.lean`
turns `true` into a guarantee about the trained model.

**Gradient descent** (`Pipeline.checkGD`). Given a feature bound `R²` for the
representation (a theorem, e.g. `morgan_bounded`), a parameter budget `B` and a tolerance
`ε`, the check is arithmetic on the hyperparameters: `λ ≥ 0`, `η > 0`,
`2η (R² + 1 + λ) ≤ 1`, `k > 0` and `B ≤ 2ηkε`. `maxStepSize` is the largest step size that
passes, and `gdTolerance` the smallest `ε` that does.

**Gradient descent, on the data** (`Pipeline.checkGDData`). The same step-size condition
with the smoothness computed exactly from the training set, `Λ = (1/m) ∑ᵣ ‖xᵣ‖² + λ`
(`smoothnessExact`), instead of bounded for every molecule: `λ ≥ 0`, `η > 0`, `2ηΛ ≤ 1`,
`k > 0`. No feature bound for the representation is needed, so the step can be as large as
the data allows (`maxStepSizeData = 1/(2Λ)`), and the guarantee is the rate itself:
`L(θ) ≤ L(u) + ‖u‖² / (2ηk)` for every `u` (`gdRate = 1/(2ηk)`).

**Jacobi and Gauss–Seidel** (`Pipeline.checkSolver`). The generic witness check of
`LeanLearn.Regression.SolverWitness` (weighted diagonal dominance, a bound on the optimum,
the certified excess `Γ β² ρ²ᵏ` below `ε`), run on the pipeline's exact normal equations.
`suggestWitness` proposes the unit-weight witness and `certifiedSolverExcess` is the bound
it certifies, if it passes.

**After training** (`Pipeline.checkResidual`). The trained parameters, read exactly, are
checked against the exact normal equations: `‖A θ - b‖² ≤ ε λ`. No condition on `A`, any
`λ > 0`, any solver in any arithmetic; `residualExcess` is the bound `‖A θ - b‖² / λ` the
residual certifies.

The check is plain `ℚ` arithmetic on the data, so `decide +kernel` can run it whenever the
kernel can evaluate the representation (`bondOrders`, but not `morgan`, whose hashing the
kernel cannot reduce).
-/

@[expose] public section

namespace Pipelines

open LeanLearn LeanLearn.Regression

namespace Pipeline

variable {m d : ℕ} (p : Pipeline m d)

/-- The number of iterations, for the Jacobi and Gauss–Seidel algorithms. -/
def solverIters : Algorithm → Option ℕ
  | .jacobi k => some k
  | .gaussSeidel k => some k
  | .gradientDescent _ _ => none

/-- Check a Jacobi/Gauss–Seidel witness against the pipeline's data, exactly. -/
def checkSolver (W : SolverWitness (d + 1)) (ε : ℚ) : Bool :=
  match solverIters p.algorithm with
  | some k =>
    decide (0 ≤ p.ridge) &&
      W.check p.exactProblem.normalMatrix p.exactProblem.normalVector k ε
  | none => false

/-- The unit-weight witness for the pipeline's normal equations. -/
def suggestWitness : SolverWitness (d + 1) :=
  SolverWitness.unitWeights p.exactProblem.normalMatrix p.exactProblem.normalVector

/-- The excess loss a witness certifies for this pipeline (`0` iterations for gradient
descent, which has its own certificate). -/
def certifiedExcess (W : SolverWitness (d + 1)) : ℚ :=
  W.excess p.exactProblem.normalMatrix ((solverIters p.algorithm).getD 0)

/-- The excess loss the suggested witness certifies, if it passes the check: how close to
the optimum Jacobi or Gauss–Seidel is guaranteed to end. `none` when the check fails. -/
def certifiedSolverExcess : Option ℚ :=
  let W := p.suggestWitness
  let e := p.certifiedExcess W
  if p.checkSolver W e then some e else none

/-! ### After training: the residual certificate -/

/-- The exact residual check on parameters `θ` — the trained `Float` model read exactly, say:
`λ > 0` and `‖A θ - b‖² ≤ ε λ` on the pipeline's exact normal equations. Soundness:
`checkResidual_sound`. -/
def checkResidual (θ : Vec ℚ (d + 1)) (ε : ℚ) : Bool := p.exactProblem.checkResidual θ ε

/-- `‖A θ - b‖² / λ`: the excess training loss the residual at `θ` certifies. -/
def residualExcess (θ : Vec ℚ (d + 1)) : ℚ := p.exactProblem.residualExcess θ

/-! ### Gradient descent -/

/-- Check a gradient-descent certificate: feature bound `R²` (proved separately for the
representation), parameter budget `B`, tolerance `ε`. -/
def checkGD (R2 B ε : ℚ) : Bool :=
  match p.algorithm with
  | .gradientDescent η k =>
    decide (0 ≤ p.ridge) && decide (0 < η) && decide (2 * η * (R2 + 1 + p.ridge) ≤ 1) &&
      decide (0 < k) && decide (B ≤ 2 * η * k * ε)
  | _ => false

/-- The largest step size the gradient-descent certificate accepts for feature bound `R²`:
`1 / (2 (R² + 1 + λ))`. -/
def maxStepSize (R2 : ℚ) : ℚ := 1 / (2 * (R2 + 1 + p.ridge))

/-- The smallest tolerance the gradient-descent certificate gives for budget `B`:
`B / (2ηk)` (`0` for the other algorithms). -/
def gdTolerance (B : ℚ) : ℚ :=
  match p.algorithm with
  | .gradientDescent η k => B / (2 * η * k)
  | _ => 0

/-! ### Gradient descent, on the data -/

/-- `Λ = (1/m) ∑ᵣ ‖xᵣ‖² + λ` of the pipeline's exact problem (`Problem.smoothnessExact`):
the smoothness the step-size condition is about, computed from this training set rather
than bounded for every molecule. -/
def smoothnessExact : ℚ := p.exactProblem.smoothnessExact

/-- The gradient-descent check on the data: `λ ≥ 0`, `η > 0`, `2ηΛ ≤ 1` with `Λ` the exact
smoothness of this training set, and `k > 0`. Nothing about the representation is assumed,
so the step size can be as large as the data allows (`maxStepSizeData`). Soundness
(`checkGDData_sound`): `L(θ) ≤ L(u) + ‖u‖² / (2ηk)` for **every** `u`. -/
def checkGDData : Bool :=
  match p.algorithm with
  | .gradientDescent η k =>
    decide (0 ≤ p.ridge) && decide (0 < η) && decide (2 * η * p.smoothnessExact ≤ 1) &&
      decide (0 < k)
  | _ => false

/-- The largest step size `checkGDData` accepts: `1 / (2Λ)`. -/
def maxStepSizeData : ℚ := 1 / (2 * p.smoothnessExact)

/-- The rate constant of the guarantee `checkGDData` gives, `1 / (2ηk)`: after `k` steps of
size `η`, `L(θ) ≤ L(u) + ‖u‖² / (2ηk)` for every `u` (`0` for the other algorithms). -/
def gdRate : ℚ :=
  match p.algorithm with
  | .gradientDescent η k => 1 / (2 * η * k)
  | _ => 0

end Pipeline

end Pipelines
