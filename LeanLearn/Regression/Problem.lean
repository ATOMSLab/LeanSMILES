/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
module

public import LeanLearn.Scalar

/-!
# LeanLearn.Regression.Problem

Linear regression — the problem.

Ridge linear regression on `m` samples with `d` features, written once over the scalar
interface of `LeanLearn.Scalar`. Only the polynomial fragment (`PolynomialLike`) and
division are used, so the same definitions run in three readings:

* `ℚ` — exact; the certificates in `Pipelines/` compute the normal equations here;
* `Float` — execution;
* `ℝ` — the theorems in `Proofs/Regression/`.

Sums are `sumFin` from `LeanLearn.Scalar` (a fold over `List.finRange n`; `Float` has no
`Finset.sum`); over `ℝ` they are `Finset.sum`s (`sumFin_eq_sum`).

**The problem.** Write `xᵣ ∈ ℝᵈ⁺¹` for sample `r` with a constant `1` appended (so
`θ = (w, b)` includes the bias), `yᵣ` for its target, and `λ ≥ 0` for the ridge penalty.
The loss is

  `L(θ) = (1/m) ∑ᵣ (⟪xᵣ, θ⟫ - yᵣ)² + λ ‖θ‖²`,

`λ = 0` being ordinary least squares. Its gradient is `2 (A θ - b)` for the **normal
equations** `A θ = b`:

  `A = (1/m) ∑ᵣ xᵣ xᵣᵀ + λ I`,  `b = (1/m) ∑ᵣ yᵣ xᵣ`.

Every solver in `Solvers.lean` works on `(A, b)`.
-/

@[expose] public section

namespace LeanLearn.Regression

/-- A length-`n` vector. -/
abbrev Vec (K : Type) (n : ℕ) := Vector K n

/-- An `m × n` matrix, stored as `m` rows. -/
abbrev Mat (K : Type) (m n : ℕ) := Vector (Vector K n) m

section Polynomial

variable {K : Type} [PolynomialLike K] {m n : ℕ}

/-- The count `n` as a scalar, by repeated addition (no `NatCast` needed). -/
def count (n : ℕ) : K := nsmulGen n 1

def dot (u v : Vec K n) : K := sumFin fun i : Fin n ↦ u[i] * v[i]

def matVec (A : Mat K m n) (v : Vec K n) : Vec K m := Vector.ofFn fun i ↦ dot A[i] v

def vsub (u v : Vec K n) : Vec K n := Vector.ofFn fun i ↦ u[i] - v[i]

def vadd (u v : Vec K n) : Vec K n := Vector.ofFn fun i ↦ u[i] + v[i]

def smul (c : K) (v : Vec K n) : Vec K n := Vector.ofFn fun i ↦ c * v[i]

def vzero : Vec K n := Vector.ofFn fun _ ↦ 0

/-- Append the constant feature `1`, so an affine model `⟪w, x⟫ + b` is the linear model
`⟪(w, b), (x, 1)⟫`. -/
def augment (x : Vec K n) : Vec K (n + 1) := x.push 1

/-- The prediction `⟪(w, b), (x, 1)⟫` of parameters `θ` on features `x`. -/
def predict (θ : Vec K (n + 1)) (x : Vec K n) : K := dot θ (augment x)

end Polynomial

/-- A ridge regression problem: `m` samples of `d` features, targets, and the ridge
penalty `λ` (`0` for ordinary least squares). -/
structure Problem (K : Type) (m d : ℕ) where
  X : Mat K m d
  y : Vec K m
  ridge : K

namespace Problem

variable {K L : Type} {m d : ℕ}

/-- Apply `f` to every number of the problem: how exact `ℚ` data is read as `Float` or
`ℝ` (`f = RatEmbed.ofRat`). -/
def map (f : K → L) (P : Problem K m d) : Problem L m d :=
  { X := P.X.map (·.map f), y := P.y.map f, ridge := f P.ridge }

variable [PolynomialLike K] [Div K] (P : Problem K m d)

/-- Sample `r` with the constant `1` appended. -/
def row (r : Fin m) : Vec K (d + 1) := augment P.X[r]

/-- The design matrix: every sample with the constant `1` appended. -/
def design : Mat K m (d + 1) := Vector.ofFn P.row

/-- `A = (1/m) ∑ᵣ xᵣ xᵣᵀ + λ I`. -/
def normalMatrix : Mat K (d + 1) (d + 1) :=
  let X := P.design
  Vector.ofFn fun i ↦ Vector.ofFn fun j ↦
    sumFin (fun r : Fin m ↦ X[r][i] * X[r][j]) / count m + if i = j then P.ridge else 0

/-- `b = (1/m) ∑ᵣ yᵣ xᵣ`. -/
def normalVector : Vec K (d + 1) :=
  let X := P.design
  Vector.ofFn fun i ↦ sumFin (fun r : Fin m ↦ X[r][i] * P.y[r]) / count m

/-- The ridge loss `L(θ) = (1/m) ∑ᵣ (⟪xᵣ, θ⟫ - yᵣ)² + λ ‖θ‖²`. -/
def loss (θ : Vec K (d + 1)) : K :=
  sumFin (fun r : Fin m ↦ (dot (P.row r) θ - P.y[r]) * (dot (P.row r) θ - P.y[r])) / count m +
    P.ridge * dot θ θ

end Problem

end LeanLearn.Regression
