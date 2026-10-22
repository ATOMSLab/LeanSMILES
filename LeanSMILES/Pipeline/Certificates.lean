/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
import LeanSMILES.Pipeline.Pipeline

/-!
# LeanSMILES.Pipeline.Certificates

Certificate checks.

Exact `ℚ` computations that decide whether a pipeline can be certified, before training.
Each check returns a `Bool`; its soundness theorem in `Proofs/Pipeline/Certificates.lean`
turns `true` into a guarantee about the trained model.

**Gradient descent** (`Pipeline.checkGD`). Given a feature bound `R²` for the
representation (a theorem, e.g. `morgan_bounded`), a parameter budget `B` and a tolerance
`ε`, the check is arithmetic on the hyperparameters: `λ ≥ 0`, `η > 0`,
`2η (R² + 1 + λ) ≤ 1`, `k > 0` and `B ≤ 2ηkε`. `maxStepSize` is the largest step size that
passes, and `gdTolerance` the smallest `ε` that does.

**Jacobi and Gauss–Seidel** (`SolverWitness`). The witness is a weight vector `w > 0`, a
ratio `ρ < 1` and a bound `β`. The check computes the normal equations `A θ = b` of the
pipeline exactly and verifies, row by row,

* `Aᵢᵢ > 0` and `∑_{j≠i} |Aᵢⱼ| wⱼ ≤ ρ Aᵢᵢ wᵢ` (weighted diagonal dominance), and
* `|bᵢ| ≤ (1 - ρ) Aᵢᵢ wᵢ β` (so the optimum has `|θ*ᵢ| ≤ β wᵢ`),

then that the certified excess loss `Γ β² ρ²ᵏ` (`Γ = ∑ᵢⱼ |Aᵢⱼ| wᵢ wⱼ`, `k` iterations) is
at most the tolerance `ε`. `SolverWitness.unitWeights` proposes a witness (`w = 1`, the
smallest `ρ` and `β` that work), and `SolverWitness.excess` is the bound it certifies.

The check is plain `ℚ` arithmetic on the data, so `decide +kernel` can run it whenever the
kernel can evaluate the representation (`bondOrders`, but not `morgan`, whose hashing the
kernel cannot reduce).
-/

namespace LeanSMILES

open Regression

namespace Check

variable {n : ℕ}

/-- `∑_{j≠i} |Aᵢⱼ| wⱼ`, exactly. -/
def offDiagWeight (A : Mat ℚ n n) (w : Vec ℚ n) (i : Fin n) : ℚ :=
  sumFin fun j ↦ if j = i then 0 else |A[i][j]| * w[j]

/-- `Γ = ∑ᵢⱼ |Aᵢⱼ| wᵢ wⱼ`, exactly. -/
def weightedMass (A : Mat ℚ n n) (w : Vec ℚ n) : ℚ :=
  sumFin fun i ↦ sumFin fun j ↦ |A[i][j]| * w[i] * w[j]

/-- The largest value of `f` over `Fin n` (`0` if `n = 0` or all values are negative). -/
def maxFin (f : Fin n → ℚ) : ℚ := (List.finRange n).foldl (fun acc i ↦ max acc (f i)) 0

end Check

/-- A witness for a Jacobi or Gauss–Seidel certificate on an `n × n` system. -/
structure SolverWitness (n : ℕ) where
  /-- Positive weights `w`. -/
  weights : Vector ℚ n
  /-- The contraction ratio `ρ < 1`. -/
  ratio : ℚ
  /-- A bound `β` with `|θ*ᵢ| ≤ β wᵢ` for the optimum `θ*`. -/
  bound : ℚ

instance {n : ℕ} : Repr (SolverWitness n) where
  reprPrec W _ :=
    s!"\{ weights := {repr W.weights.toList}, ratio := {repr W.ratio}, bound := {repr W.bound} }"


namespace SolverWitness

variable {n : ℕ}

/-- The excess loss the witness certifies after `k` iterations: `Γ β² ρ²ᵏ`. -/
def excess (W : SolverWitness n) (A : Mat ℚ n n) (k : ℕ) : ℚ :=
  Check.weightedMass A W.weights * W.bound ^ 2 * npowGen W.ratio (2 * k)

/-- Check the witness on `A θ = b` for `k` iterations and tolerance `ε`. -/
def check (W : SolverWitness n) (A : Mat ℚ n n) (b : Vec ℚ n) (k : ℕ) (ε : ℚ) : Bool :=
  decide (0 ≤ W.ratio) && decide (W.ratio < 1) && decide (0 ≤ W.bound) &&
    (List.finRange n).all (fun i ↦
      decide (0 < W.weights[i]) && decide (0 < A[i][i]) &&
        decide (Check.offDiagWeight A W.weights i ≤ W.ratio * A[i][i] * W.weights[i]) &&
        decide (|b[i]| ≤ (1 - W.ratio) * A[i][i] * W.weights[i] * W.bound)) &&
    decide (W.excess A k ≤ ε)

/-- The unit-weight witness: `ρ = maxᵢ (∑_{j≠i} |Aᵢⱼ|) / Aᵢᵢ` and
`β = maxᵢ |bᵢ| / ((1 - ρ) Aᵢᵢ)`. It checks exactly when `A` is strictly diagonally
dominant (with positive diagonal). -/
def unitWeights (A : Mat ℚ n n) (b : Vec ℚ n) : SolverWitness n :=
  let w : Vector ℚ n := Vector.replicate n 1
  let ρ := Check.maxFin fun i ↦ Check.offDiagWeight A w i / A[i][i]
  { weights := w, ratio := ρ, bound := Check.maxFin fun i ↦ |b[i]| / ((1 - ρ) * A[i][i]) }

end SolverWitness

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

end Pipeline

end LeanSMILES
