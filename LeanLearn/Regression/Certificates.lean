/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
module

public import LeanLearn.Regression.Solvers

/-!
# LeanLearn.Regression.Certificates

Certificate checks for the iterative solvers.

Exact `ℚ` computations on a linear system `A θ = b` that decide, before running Jacobi or
Gauss–Seidel, how close to the solution `k` steps are guaranteed to end. The check returns a
`Bool`; its soundness theorem in `Proofs/Regression/Certificates.lean` turns `true` into a
guarantee about the iterate.

**Jacobi and Gauss–Seidel** (`SolverWitness`). The witness is a weight vector `w > 0`, a
ratio `ρ < 1` and a bound `β`. The check verifies, row by row,

* `Aᵢᵢ > 0` and `∑_{j≠i} |Aᵢⱼ| wⱼ ≤ ρ Aᵢᵢ wᵢ` (weighted diagonal dominance), and
* `|bᵢ| ≤ (1 - ρ) Aᵢᵢ wᵢ β` (so the solution has `|θ*ᵢ| ≤ β wᵢ`),

then that the certified excess loss `Γ β² ρ²ᵏ` (`Γ = ∑ᵢⱼ |Aᵢⱼ| wᵢ wⱼ`, `k` iterations) is
at most the tolerance `ε`. `SolverWitness.unitWeights` proposes a witness (`w = 1`, the
smallest `ρ` and `β` that work), and `SolverWitness.excess` is the bound it certifies.

The check is plain `ℚ` arithmetic on the data, so `decide +kernel` can run it whenever the
kernel can evaluate `A` and `b`.

The gradient-descent certificate needs no data, only a bound on the features, so it is
stated where the features come from (for molecules, `Pipelines/Certificates.lean`).
-/

@[expose] public section

namespace LeanLearn.Regression

namespace Check

variable {n : ℕ}

/-- `∑_{j≠i} |Aᵢⱼ| wⱼ`, exactly. -/
def offDiagWeight (A : Mat ℚ n n) (w : Vec ℚ n) (i : Fin n) : ℚ :=
  sumFin fun j : Fin n ↦ if j = i then 0 else |A[i][j]| * w[j]

/-- `Γ = ∑ᵢⱼ |Aᵢⱼ| wᵢ wⱼ`, exactly. -/
def weightedMass (A : Mat ℚ n n) (w : Vec ℚ n) : ℚ :=
  sumFin fun i : Fin n ↦ sumFin fun j : Fin n ↦ |A[i][j]| * w[i] * w[j]

/-- The largest value of `f` over `Fin n` (`0` if `n = 0` or all values are negative). -/
def maxFin (f : Fin n → ℚ) : ℚ := (List.finRange n).foldl (fun acc i ↦ max acc (f i)) 0

end Check

/-- A witness for a Jacobi or Gauss–Seidel certificate on an `n × n` system. -/
structure SolverWitness (n : ℕ) where
  /-- Positive weights `w`. -/
  weights : Vector ℚ n
  /-- The contraction ratio `ρ < 1`. -/
  ratio : ℚ
  /-- A bound `β` with `|θ*ᵢ| ≤ β wᵢ` for the solution `θ*`. -/
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
  let ρ := Check.maxFin fun i : Fin n ↦ Check.offDiagWeight A w i / A[i][i]
  { weights := w, ratio := ρ, bound := Check.maxFin fun i : Fin n ↦ |b[i]| / ((1 - ρ) * A[i][i]) }

end SolverWitness

end LeanLearn.Regression
