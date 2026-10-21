module

public import LeanSMILES.API.Features
public import LeanSMILES.API.Metrics
public import LeanSMILES.API.Stats
public import LeanSMILES.SMILES.Executables

/-!
# SMILES → solubility pipeline

The last step of the notebook: take a SMILES string from a user, validate it, featurize
it, and predict log solubility with a trained fingerprint model.
-/

@[expose] public section

namespace API

open Primitives ML Chem

/-- A linear model on radius-`radius`, `nBits`-bit Morgan fingerprints. -/
structure FingerprintModel (α : Type) (nBits : Nat) where
  radius : Nat
  model : LinearModel α nBits

/-- Parse and validate a SMILES string (well-formed, at least one atom). -/
def parseValid (s : String) : Except String Molecule := Chem.Exec.molFromSmiles s

/-- Predicted log solubility (log₁₀ mol/L) for a SMILES string. -/
def FingerprintModel.predict {α : Type} [Scalar α] {nBits : Nat} (fm : FingerprintModel α nBits)
    (s : String) : Except String α := do
  let m ← parseValid s
  return fm.model.score (moleculeFingerprint fm.radius nBits m)

/-- The notebook's `predict_wavelength_from_smiles`, for solubility. -/
def predictSolubilityMessage {nBits : Nat} (fm : FingerprintModel Float nBits) (s : String) :
    String :=
  match fm.predict s with
  | .ok y => s!"Predicted log solubility: {formatFloat y 2} log(mol/L)"
  | .error e => s!"Invalid SMILES string ({e}); please enter a valid SMILES string"

def RegressionMetrics.format (r : RegressionMetrics Float) : String :=
  s!"RMSE {formatFloat r.rmse 3}  MAE {formatFloat r.mae 3}  R² {formatFloat r.r2 3}"

end API

end
