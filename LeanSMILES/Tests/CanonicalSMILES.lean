import LeanSMILES.SMILES.Definitions
import LeanSMILES.MetaPrograms.Test

/-! Tests for canonical ranking and `canonicalSMILES`. -/

open Chem

def canon (s : String) : String :=
  match (SMILES.mk s).canonicalize with
  | .ok c => c.smiles.str
  | .error e => s!"error: {e}"

-- different spellings of the same molecule give the same string
#test canon "CCO" == "CCO" && canon "OCC" == "CCO"
#test canon "OC(C)=O" == "CC(=O)O"
#test canon "c1ccc(cc1)" == "c1ccccc1"
#test canon "[CH4]" == canon "C"
#test canon "Oc1ccccc1C" == canon "Cc1ccccc1O"
#test canon "C1CC1C" == canon "CC1CC1"
#test canon "C(C)(C)(C)C" == canon "CC(C)(C)C"
#test canon "c1cccc2c1cccc2" == canon "c1ccc2ccccc2c1"
#test canon "[Cl-].[Na+]" == canon "[Na+].[Cl-]"
#test canon "OC(=O)CN" == canon "NCC(=O)O"
#test canon "CC(C)Cc1ccc(cc1)C(C)C(=O)O" == canon "OC(=O)C(C)c1ccc(CC(C)C)cc1"

-- different molecules give different strings
#test canon "CCO" != canon "COC"
#test canon "CC=O" != canon "C=CO"
#test canon "c1ccncc1" != canon "c1ccccc1"

-- canonical forms are fixed points
#test ["CCO", "CC(=O)O", "c1ccccc1", "C1CC2CCC1C2", "CN1C=NC2=C1C(=O)N(C(=O)N2C)C",
        "CC(C)Cc1ccc(cc1)C(C)C(=O)O"].all fun s => (SMILES.mk (canon s)).isCanonical

#test (SMILES.mk "CCO").sameMolecule ⟨"OCC"⟩
#test !(SMILES.mk "CCO").sameMolecule ⟨"COC"⟩
#test !(SMILES.mk "C1CC").isCanonical
