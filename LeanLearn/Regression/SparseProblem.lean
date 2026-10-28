/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanLearn.Regression.Certificates

/-!
# LeanLearn.Regression.SparseProblem

The residual certificate on sparse `0/1` features, exactly.

`SparseRidge.fit` trains scikit-learn's `Ridge(alpha)` objective on Morgan bits — a sample is
the list of its on-bits — in `Float`, by conjugate gradients, with the intercept unpenalised:

  `Σᵣ (yᵣ − w · xᵣ − b)² + α ‖w‖²`.

That is a `Problem` (`LeanLearn.Regression.Problem`) in disguise. Centre the data — every bit
column on its training mean `x̄ⱼ`, the target on `ȳ` — and set `λ = α / m`: at `θ = (w, 0)`,
`m · Problem.loss θ` is the objective above at its optimal intercept `b = ȳ − x̄ · w`, and on
centred data the optimal intercept of `Problem.loss` itself is `0`. So the trained weights,
read exactly and padded with a zero bias, can be checked by `Problem.checkResidual` and are
covered by `Problem.checkResidual_sound` — provided the residual can be computed.

`Problem.residualAt` forms the `(d + 1) × (d + 1)` normal matrix, dense: for 2048 bits that is
hundreds of millions of exact rationals per fit. `SparseProblem.residual` computes the same
vector from the bit lists, `(1/m) Xcᵀ (Xc θ − y) + λ θ` with the centring applied on the fly
(`Xc θ = X θ − (x̄ · θ) 1` and `Xcᵀ v = Xᵀ v − x̄ (Σ v)`), in a few tens of thousands of
operations. `SparseProblem.residual_eq` (`Proofs/Regression/SparseProblem.lean`) proves it
equal to `Problem.residualAt` of the dense problem `SparseProblem.toProblem`, so the
certificate theorem applies verbatim: `SparseProblem.checkResidual_sound`.
-/

@[expose] public section

namespace LeanLearn.Regression

/-- A ridge regression problem on sparse `0/1` features: `m` samples, each the list of its
on-bits among `d` (a bit listed twice counts twice), their targets, and the ridge penalty
`λ` of the centred dense problem `toProblem` — `α / m` for scikit-learn's `alpha`. -/
structure SparseProblem (m d : ℕ) where
  bits : Vector (List (Fin d)) m
  y : Vec ℚ m
  ridge : ℚ

namespace SparseProblem

variable {m d : ℕ}

/-- `acc` with `c` added at every index in `l` (at an index listed twice, twice). -/
def addAt (acc : Vec ℚ d) (c : ℚ) (l : List (Fin d)) : Vec ℚ d :=
  l.foldl (fun acc (j : Fin d) ↦ acc.set j (acc[j] + c)) acc

/-- `Xᵀ v` on the raw bits — entry `j` is `Σᵣ xᵣⱼ vᵣ` with `xᵣⱼ` the count of `j` in row `r` —
by scatter-add over the rows (`scatter_getElem`). -/
def scatter (bits : Vector (List (Fin d)) m) (v : Vec ℚ m) : Vec ℚ d :=
  (List.finRange m).foldl (fun acc r ↦ addAt acc v[r] bits[r]) vzero

variable (S : SparseProblem m d)

/-- The bit means `x̄ⱼ = (1/m) Σᵣ xᵣⱼ`. -/
def means : Vec ℚ d := (scatter S.bits (Vector.replicate m 1)).map (· / m)

/-- The target mean `ȳ`. -/
def yMean : ℚ := sumFin (fun r : Fin m ↦ S.y[r]) / m

/-- The dense problem: bit counts centred on their means, targets centred on theirs, the
same `λ`. Never formed for 2048 bits; it is what `residual` and `loss` are proved equal to. -/
def toProblem : Problem ℚ m d :=
  { X := Vector.ofFn fun r ↦ Vector.ofFn fun j ↦ (S.bits[r].count j : ℚ) - S.means[j]
    y := Vector.ofFn fun r ↦ S.y[r] - S.yMean
    ridge := S.ridge }

/-- The errors `⟪xᵣ, θ⟫ − yᵣ` of the centred problem at `θ = (w, b)`, from the bit lists:
`Σ_{j ∈ row r} wⱼ − x̄ · w + b − (yᵣ − ȳ)` (`errors_getElem`). -/
def errors (θ : Vec ℚ (d + 1)) : Vec ℚ m :=
  let xbar := S.means
  let ybar := S.yMean
  let shift := sumFin fun j : Fin d ↦ xbar[j] * θ[j.castSucc]
  Vector.ofFn fun r ↦
    sumGen S.bits[r] (fun j ↦ θ[j.castSucc]) - shift + θ[Fin.last d] - (S.y[r] - ybar)

/-- The residual `A θ − b` of the centred problem's normal equations, from the bit lists:
`(1/m) Xcᵀ e + λ θ` with `e` the errors and `Xcᵀ e = Xᵀ e − x̄ (Σ e)`; the bias row is
`(1/m) Σ e + λ b`. Equal to `Problem.residualAt` of `toProblem` (`residual_eq`). -/
def residual (θ : Vec ℚ (d + 1)) : Vec ℚ (d + 1) :=
  let e := S.errors θ
  let total := sumFin fun r : Fin m ↦ e[r]
  let acc := scatter S.bits e
  let xbar := S.means
  (Vector.ofFn fun j : Fin d ↦ (acc[j] - xbar[j] * total) / m + S.ridge * θ[j.castSucc]).push
    (total / m + S.ridge * θ[Fin.last d])

/-- The ridge loss `L(θ) = (1/m) Σᵣ eᵣ² + λ ‖θ‖²` of the centred problem, from the bit lists
(`loss_eq`). -/
def loss (θ : Vec ℚ (d + 1)) : ℚ :=
  let e := S.errors θ
  sumFin (fun r : Fin m ↦ e[r] * e[r]) / m + S.ridge * dot θ θ

/-- `‖A θ − b‖² / λ`: the excess loss the residual at `θ` certifies
(`residualExcess_eq`, `Problem.checkResidual_sound`). -/
def residualExcess (θ : Vec ℚ (d + 1)) : ℚ :=
  let r := S.residual θ
  dot r r / S.ridge

/-- The a posteriori check on parameters `θ`, from the bit lists: `λ > 0` and
`‖A θ − b‖² ≤ ε λ`. The same `Bool` as `Problem.checkResidual` on `toProblem`
(`checkResidual_eq`); a pass puts `θ` within `ε` of the optimum (`checkResidual_sound`). -/
def checkResidual (θ : Vec ℚ (d + 1)) (ε : ℚ) : Bool :=
  let r := S.residual θ
  decide (0 < S.ridge) && decide (dot r r ≤ ε * S.ridge)

end SparseProblem

end LeanLearn.Regression
