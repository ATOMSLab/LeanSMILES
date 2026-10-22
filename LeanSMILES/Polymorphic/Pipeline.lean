module

public import LeanSMILES.Polymorphic.Chem.Representation
public import LeanSMILES.Polymorphic.ML.Algorithm
public import LeanSMILES.Polymorphic.ML.Metrics

/-!
# Cheminformatics pipelines

A pipeline is the whole specification of a model: labelled molecules, a molecular
representation, and a learning algorithm with its hyperparameters.

```
molecules ──representation──▶ feature matrix X ──algorithm──▶ linear model ──▶ predictions
 targets  ─────────────────────────▶ y ──────────────┘
```

It is a value, written once for any `Scalar`. At `α := Float` it trains and predicts
(`Float/Pipeline.lean`). At `α := ℝ`, `Proofs/Pipeline.lean` proves what the trained
model is guaranteed to satisfy, from conditions on the pipeline's parameters that can be
checked without training it.
-/

@[expose] public section

namespace LeanSMILES

open Primitives Chem ML

/-- `m` molecules with targets: real values for regression, `±1` labels for
classification. -/
structure LabelledMolecules (α : Type) (m : Nat) where
  molecules : Vector Molecule m
  targets : Vec α m

namespace LabelledMolecules

variable {α : Type} [Scalar α] {m : Nat}

/-- Parse `(SMILES, target)` pairs; fails on the first string that is not a well-formed,
non-empty molecule. -/
def ofSMILES (entries : Vector (String × α) m) : Except String (LabelledMolecules α m) := do
  let molecules ← entries.mapM fun (s, _) => do
    let mol ← (SMILES.mk s.trimAscii.toString).parse
    unless decide mol.WellFormed do throw s!"{s}: bond refers to a missing atom"
    unless 0 < mol.size do throw s!"{s}: empty molecule"
    return mol
  return { molecules, targets := entries.map (·.2) }

/-- Class labels: `1` for targets `≥ t`, `-1` below. -/
def binarize (t : α) (d : LabelledMolecules α m) : LabelledMolecules α m :=
  { d with targets := d.targets.map fun y => if t ≤ y then 1 else -1 }

end LabelledMolecules

/-- A cheminformatics pipeline: data, a representation with `n` features, and a learning
algorithm. -/
structure Pipeline (α : Type) (m n : Nat) where
  data : LabelledMolecules α m
  representation : Representation α n
  algorithm : Algorithm α

namespace Pipeline

variable {α : Type} [Scalar α] {m n : Nat}

/-- The feature matrix (one row per molecule) and the targets. -/
@[specialize] def dataset (p : Pipeline α m n) : Dataset α m n :=
  { X := p.data.molecules.map p.representation.featurize, y := p.data.targets }

/-- The trained model. -/
@[specialize] def model (p : Pipeline α m n) : LinearModel α n := p.algorithm.fit p.dataset

/-- Score of a molecule under a trained model: predicted target for regression, signed
score for classification. -/
@[specialize] def predictWith (p : Pipeline α m n) (model : LinearModel α n) (mol : Molecule) :
    α :=
  model.score (p.representation.featurize mol)

/-- Train, then score a molecule. To score many molecules, train once with `model` and
use `predictWith`. -/
@[specialize] def predict (p : Pipeline α m n) (mol : Molecule) : α := p.predictWith p.model mol

/-- Mean squared error of the trained model on its training data. -/
@[specialize] def trainMSE (p : Pipeline α m n) : α := mse p.model p.dataset

/-- Fraction of training molecules whose `±1` label the trained model gets right. -/
@[specialize] def trainAccuracy (p : Pipeline α m n) : α :=
  accuracy p.dataset.y (p.model.predictAll p.dataset.X)

end Pipeline

end LeanSMILES

end
