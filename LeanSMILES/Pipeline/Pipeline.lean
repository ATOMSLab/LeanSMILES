/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
import LeanSMILES.Pipeline.Representation
import LeanSMILES.Regression.Solvers

/-!
# LeanSMILES.Pipeline.Pipeline

Cheminformatics pipelines.

A pipeline is the whole specification of a model:

```
SMILES ──parse──▶ Mol ──representation──▶ features (ℚ) ─┐
targets (ℚ) ─────────────────────────────────────────────┴─▶ ridge regression problem
                                    ──algorithm (GD / Jacobi / Gauss–Seidel)──▶ θ
```

The data, the representation and the hyperparameters are exact rationals
(`exactProblem`). The solver runs in any scalar type with a `RatEmbed`: `Float` to
execute, `ℝ` for the theorems in `Proofs/Pipeline/Certificates.lean`, which certify the
trained model from conditions checked without training it.
-/

namespace LeanSMILES

open Regression

/-- `m` molecules with exact rational targets. -/
structure LabelledMolecules (m : ℕ) where
  molecules : Vector Mol m
  targets : Vector ℚ m

namespace LabelledMolecules

variable {m : ℕ}

/-- Parse `(SMILES, target)` pairs. -/
def ofSmiles (entries : Vector (String × ℚ) m) : Except String (LabelledMolecules m) := do
  let molecules ← entries.mapM fun (s, _) ↦
    match SMILES.parse s with
    | .ok M => .ok M
    | .error e => .error s!"{s}: {e}"
  return { molecules, targets := entries.map (·.2) }

/-- Parse `(SMILES, target)` pairs, or panic: for examples and tests, like
`Mol.ofSmiles!`. -/
def ofSmiles! (entries : Vector (String × ℚ) m) : LabelledMolecules m :=
  { molecules := entries.map fun (s, _) ↦ Mol.ofSmiles! s, targets := entries.map (·.2) }

/-- The targets as `Float`s, for display. -/
def targetsFloat (D : LabelledMolecules m) : Vector Float m := D.targets.map Rat.toFloat

/-- The canonical SMILES of every molecule. -/
def canonicalSmiles (D : LabelledMolecules m) : Vector String m :=
  D.molecules.map Mol.canonicalSmiles

/-- No molecule occurs twice, whatever SMILES it was written with. -/
def noDuplicates (D : LabelledMolecules m) : Bool := decide D.canonicalSmiles.toList.Nodup

end LabelledMolecules

/-- A cheminformatics pipeline: labelled molecules, a representation with `d` features, a
ridge penalty (`0` for ordinary least squares) and an iterative solver. -/
structure Pipeline (m d : ℕ) where
  data : LabelledMolecules m
  representation : Representation d
  ridge : ℚ := 0
  algorithm : Algorithm

namespace Pipeline

variable {m d : ℕ} (p : Pipeline m d)

/-- The regression problem, exactly: features, targets and penalty over `ℚ`. -/
def exactProblem : Problem ℚ m d :=
  { X := p.data.molecules.map p.representation, y := p.data.targets, ridge := p.ridge }

/-- The regression problem read in a scalar type. -/
def problem (K : Type) [RatEmbed K] : Problem K m d := p.exactProblem.map RatEmbed.ofRat

/-- The trained parameters `θ = (w, b)`. -/
def model (K : Type) [PolynomialLike K] [Div K] [BEq K] [RatEmbed K] : Vec K (d + 1) :=
  p.algorithm.fit (p.problem K)

/-- The training loss of the trained model. -/
def trainLoss (K : Type) [PolynomialLike K] [Div K] [BEq K] [RatEmbed K] : K :=
  (p.problem K).loss (p.model K)

/-- The prediction of parameters `θ` on a molecule. -/
def predictWith {K : Type} [PolynomialLike K] [Div K] [BEq K] [RatEmbed K] (θ : Vec K (d + 1))
    (M : Mol) : K :=
  predict θ ((p.representation M).map RatEmbed.ofRat)

/-- The prediction of parameters `θ` on a SMILES string (panics if it does not parse). -/
def predictSmiles {K : Type} [PolynomialLike K] [Div K] [BEq K] [RatEmbed K]
    (θ : Vec K (d + 1)) (s : String) : K :=
  p.predictWith θ (Mol.ofSmiles! s)

/-- The predictions of parameters `θ` on every molecule of a dataset. -/
def predictAll {K : Type} [PolynomialLike K] [Div K] [BEq K] [RatEmbed K] {k : ℕ}
    (θ : Vec K (d + 1)) (D : LabelledMolecules k) : Vector K k :=
  D.molecules.map (p.predictWith θ)

/-- The mean squared error of parameters `θ` on a dataset, with this pipeline's
representation (no ridge penalty): the test error, on held-out molecules. -/
def mse {K : Type} [PolynomialLike K] [Div K] [BEq K] [RatEmbed K] {k : ℕ}
    (θ : Vec K (d + 1)) (D : LabelledMolecules k) : K :=
  (({ p with data := D, ridge := 0 } : Pipeline k d).problem K).loss θ

/-- The mean squared error of the trained model on its training data (no ridge
penalty). -/
def trainMSE (K : Type) [PolynomialLike K] [Div K] [BEq K] [RatEmbed K] : K :=
  p.mse (p.model K) p.data

end Pipeline

end LeanSMILES
