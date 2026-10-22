module

public import LeanSMILES.Float.ML
public import LeanSMILES.Float.Chem
public import LeanSMILES.Polymorphic.Pipeline

/-!
# Pipelines on `Float`

`Pipeline` at `α := Float`: build one from SMILES strings, train it and predict. Each
definition is the generic one (`*_eq` lemmas hold by `rfl`), so the guarantees proved in
`Proofs/Pipeline.lean` over `ℝ` are about this code, up to rounding.
-/

@[expose] public section

namespace LeanSMILES.Exec

abbrev Pipeline (m n : Nat) := LeanSMILES.Pipeline Float m n
abbrev LabelledMolecules (m : Nat) := LeanSMILES.LabelledMolecules Float m

variable {m n : Nat}

def LabelledMolecules.ofSMILES (entries : Vector (String × Float) m) :
    Except String (LabelledMolecules m) :=
  LeanSMILES.LabelledMolecules.ofSMILES entries

def Pipeline.model (p : Pipeline m n) : ML.Exec.LinearModel n := LeanSMILES.Pipeline.model p
def Pipeline.predictWith (p : Pipeline m n) (model : ML.Exec.LinearModel n)
    (mol : Chem.Molecule) : Float :=
  LeanSMILES.Pipeline.predictWith p model mol
def Pipeline.trainMSE (p : Pipeline m n) : Float := LeanSMILES.Pipeline.trainMSE p
def Pipeline.trainAccuracy (p : Pipeline m n) : Float := LeanSMILES.Pipeline.trainAccuracy p

theorem Pipeline.model_eq (p : Pipeline m n) :
    Pipeline.model p = LeanSMILES.Pipeline.model (α := Float) p := rfl

end LeanSMILES.Exec

end
