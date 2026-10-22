/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
-/
module

public import Pipelines.Data
public import Pipelines.Proofs.Certificates
-- The same modules again as `meta` imports: the `#eval`s run their code at elaboration time.
meta import Pipelines.Data
meta import Pipelines.Proofs.Certificates
-- The two `decide +kernel` certificates in section 8 make the kernel run `Array.ofFn`, `Array.map`
-- and `Fin.foldl`, whose bodies core does not expose; `import all` lets this file see them.
import all Init.Data.Array.Basic
import all Init.Data.Vector.Basic
import all Init.Data.Fin.Fold

/-!
# Examples: molecules → features → certified linear regression

Solubility prediction on the Delaney (ESOL) table, one step at a time: molecules with
exact targets, representations, the regression problem, three solvers with their
certificates, and predictions. Open this file in the editor; the Infoview shows each
`#eval`.

A *certificate* is a check run before training. Its soundness theorem
(`Pipelines/Proofs/Certificates.lean`) turns `true` into a guarantee about the trained
model; section 8 states two of them as theorems.
-/

public section

open LeanSMILES LeanLearn LeanLearn.Regression Pipelines

-- Everything here lives in `PipelineExample`, so this file can be imported next to the
-- other examples (`smiles.lean` also defines a `delaney`).
namespace PipelineExample

/-! ### 1. Data: molecules with exact targets

`CSVparser.load` reads the table (see `parsercsv.lean`). `ofRecords` parses each SMILES
into a `Mol` and keeps the measured log solubility as an exact rational. -/

def delaney := CSVparser.load "datasets/delaney-processed.csv"

def train : LabelledMolecules 40 := .ofRecords delaney 0 40   -- rows 0–39
def test : LabelledMolecules 10 := .ofRecords delaney 40 10   -- rows 40–49, held out

-- The table's decimals, exactly: -0.77 is -77/100.
#eval train.targets.toList.take 5
#eval train.canonicalSmiles.toList.take 5

-- No molecule occurs twice, however its SMILES was written.
#eval train.noDuplicates

-- Molecules can also be typed in, with their targets.
def small : LabelledMolecules 4 :=
  .ofSmiles! #v[("CCO", -77 / 100), ("CC=O", 64 / 100), ("CCC", -94 / 100), ("OCO", 1)]

#eval small.canonicalSmiles.toList

/-! ### 2. Representations

A representation turns a molecule into exact rational features, read from the toolkit's
`Mol`: Morgan bits (`morganVector`), the bond-order matrix (`adjMatrix`), or counts of
atoms, bonds and hydrogens. -/

def ethanol : Mol := Mol.ofSmiles! "CCO"

-- Morgan fingerprint bits, radius 1, folded to 16 bits.
#eval (Representation.morgan 1 16 ethanol).toList

-- The bond-order matrix of the first 3 atoms, row by row: `adjMatrix`, padded.
#eval ethanol.mol.adjMatrix
#eval (Representation.bondOrders 3 ethanol).toList

-- Atoms, bonds, hydrogens, aromatic atoms, heteroatoms.
#eval (Representation.counts ethanol).toList
#eval (Representation.counts (Mol.ofSmiles! "c1ccccc1O")).toList

-- Side by side, and clipped to `[-3, 3]` (which bounds any representation).
#eval ((Representation.counts ++ Representation.morgan 1 8) ethanol).toList
#eval (Representation.clip 3 Representation.counts (Mol.ofSmiles! "c1ccccc1O")).toList

-- The bond-order matrix follows the atom order of the SMILES ...
#eval Representation.bondOrders 3 (Mol.ofSmiles! "OCC") == Representation.bondOrders 3 ethanol
-- ... unless it is read through the canonical SMILES (`canonical_relabel`).
#eval (Representation.bondOrders 3).canonical (Mol.ofSmiles! "OCC") ==
  (Representation.bondOrders 3).canonical ethanol

/-! ### 3. The regression problem

A pipeline is data, a representation, a ridge penalty `λ` (default `0`) and a solver. Its
loss is `(1/m) ∑ᵣ (⟪xᵣ, θ⟫ - yᵣ)² + λ ‖θ‖²`, where `xᵣ` is molecule `r`'s features with a
constant `1` appended for the intercept. Every solver works on the normal equations
`A θ = b`, computed here exactly. -/

def gd : Pipeline 40 32 :=
  { data := train, representation := .morgan 2 32, algorithm := .gradientDescent (1 / 66) 3000 }

-- 33 unknowns: 32 bits and the intercept.
#eval gd.exactProblem.normalMatrix.size

-- The intercept row of `A`: how often each bit is set, over the 40 molecules.
#eval gd.exactProblem.normalMatrix[32].toList.take 8
#eval gd.exactProblem.normalVector.toList.take 4

/-! ### 4. Gradient descent and its certificate

Morgan features are `0` or `1`, so every molecule has `‖φ‖² ≤ 32` (`morgan_bounded`). With
that bound the certificate is arithmetic on `λ`, the step size and the step count; it
does not look at the data, so it holds for every dataset. -/

-- The largest step size the certificate accepts, for this representation.
#eval gd.maxStepSize 32

-- The tolerance it gives against every model with `‖θ‖² ≤ 4`: 11/250, about 0.044.
#eval gd.gdTolerance 4
#eval gd.checkGD 32 4 (1 / 20)

-- A step size twice too large fails.
#eval ({ gd with algorithm := .gradientDescent (1 / 33) 3000 }).checkGD 32 4 (1 / 20)

-- Training error, and error on the 10 held-out molecules.
#eval (gd.trainMSE Float, gd.mse (gd.model Float) test)

-- More steps never increase the loss (`loss_gradientDescent_antitone`).
#eval [0, 10, 100, 1000].map fun k ↦
  ({ gd with algorithm := .gradientDescent (1 / 66) k }).trainLoss Float

/-! ### 5. Gauss–Seidel and Jacobi

These solve the normal equations one coordinate at a time. Their certificate looks at the
data: `A` must be diagonally dominant (`∑_{j≠i} |Aᵢⱼ| wᵢ ≤ ρ Aᵢᵢ wᵢ` with `ρ < 1`). The
check is exact; `suggestWitness` proposes `w`, `ρ` and a bound `β` on the optimum, and
`certifiedSolverExcess` is how far from the optimum the solver is guaranteed to end. -/

def gs : Pipeline 40 16 :=
  { data := train, representation := .bondOrders 4, ridge := 16, algorithm := .gaussSeidel 30 }

def jac : Pipeline 40 16 := { gs with algorithm := .jacobi 30 }

#eval gs.suggestWitness
#eval gs.checkSolver gs.suggestWitness (1 / 1000)

-- After 30 sweeps, both are certified within 10⁻⁹ of the optimum, and agree.
#eval gs.certifiedSolverExcess.map fun e ↦ decide (e < 1 / 10 ^ 9)
#eval (gs.trainLoss Float, jac.trainLoss Float)

-- Gauss–Seidel never increases the loss, sweep by sweep, with no condition at all
-- (`gaussSeidel_antitone`), here without any ridge penalty.
#eval (List.range 6).map fun k ↦
  ({ gs with ridge := 0, algorithm := .gaussSeidel k }).trainLoss Float

/-! ### 6. When a check fails

With a small penalty the normal equations are far from diagonally dominant: the witness
has `ρ > 1`, and nothing is certified. Jacobi indeed diverges; Gauss–Seidel, monotone for
any data, does not. -/

def weak : Pipeline 40 16 := { gs with ridge := 1, algorithm := .jacobi 30 }

#eval weak.suggestWitness.ratio
#eval weak.certifiedSolverExcess
#eval (weak.trainLoss Float, ({ weak with algorithm := .gaussSeidel 30 }).trainLoss Float)

-- The penalty buys the certificate: `ρ` falls below `1` between `λ = 4` and `λ = 8`.
#eval [1, 4, 8, 16].map fun r ↦ (r, ({ gs with ridge := r }).suggestWitness.ratio.toFloat)

/-! ### 7. Predictions -/

def θ : Vec Float 33 := gd.model Float

-- Propan-1-ol (measured: 0.62).
#eval gd.predictSmiles θ "CCCO"

-- The held-out molecules: canonical SMILES, prediction, measured value.
#eval (test.canonicalSmiles.toList.zip
  ((gd.predictAll θ test).toList.zip test.targetsFloat.toList)).take 5

-- Test error of three representations, all with Gauss–Seidel and `λ = 1`.
#eval let p₁ : Pipeline 40 32 := { gd with ridge := 1, algorithm := .gaussSeidel 30 }
      let p₂ : Pipeline 40 16 := { gs with ridge := 1 }
      let p₃ : Pipeline 40 5 := { gs with representation := .counts, ridge := 1 }
      (p₁.mse (p₁.model Float) test, p₂.mse (p₂.model Float) test,
        p₃.mse (p₃.model Float) test)

/-! ### 8. The checks are theorems

`checkGD_sound` and `checkSolver_sound` turn a passing check into a guarantee about the
trained model, over `ℝ`. For gradient descent the check is arithmetic (`decide`); for
Gauss–Seidel and Jacobi the kernel runs the whole check — parsing the SMILES, building the
bond-order matrices, forming the normal equations — so the guarantee needs no trust in
compiled code. -/

/-- After 3000 steps, gradient descent is within `1/20` of every model with `‖θ‖² ≤ 4`. -/
theorem gd_certified (u : Vec ℝ 33) (hu : ∑ i : Fin 33, u[i] ^ 2 ≤ 4) :
    gd.trainLoss ℝ ≤ (gd.problem ℝ).loss u + 1 / 20 := by
  have := gd.checkGD_sound (R2 := (32 : ℕ)) (B := 4) (ε := 1 / 20)
    (Representation.morgan_bounded 2 32) (by decide +kernel) u (by exact_mod_cast hu)
  simpa using this

def smallJacobi : Pipeline 4 9 :=
  { data := small, representation := .bondOrders 3, ridge := 8, algorithm := .jacobi 40 }

/-- After 40 steps, Jacobi is within `1/1000` of the optimum: no parameters do better. -/
theorem smallJacobi_certified (u : Vec ℝ 10) :
    smallJacobi.trainLoss ℝ ≤ (smallJacobi.problem ℝ).loss u + 1 / 1000 := by
  have := smallJacobi.checkSolver_sound (W := smallJacobi.suggestWitness) (ε := 1 / 1000)
    (by decide +kernel) u
  simpa using this

end PipelineExample
