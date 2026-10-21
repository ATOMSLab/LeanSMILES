import LeanSMILES.API.Pipeline
import LeanSMILES.MetaPrograms.Test

/-! Tests for `parseValid`, `FingerprintModel.predict` and `predictSolubilityMessage`. -/

open Primitives ML API

-- a model whose prediction is the bias minus the number of set bits
def fm : FingerprintModel Float 64 :=
  { radius := 2, model := { weights := Vector.replicate 64 (-1.0), bias := 1.0 } }

#test (parseValid " CCO ").toOption.map (·.atoms.size) == some 3
#test (parseValid "C1CC").toOption.isNone
#test (fm.predict "C").toOption == some (1.0 - 3.0)
#test (fm.predict "CCO").toOption == some (fm.model.score (moleculeFingerprint 2 64 (
  (parseValid "CCO").toOption.getD default)))
#test predictSolubilityMessage fm "C" == "Predicted log solubility: -2.00 log(mol/L)"
#test predictSolubilityMessage fm "C1CC" ==
  "Invalid SMILES string (unclosed ring); please enter a valid SMILES string"
