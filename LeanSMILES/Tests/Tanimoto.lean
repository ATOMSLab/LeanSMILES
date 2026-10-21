import LeanSMILES.SMILES.EXECUTABLES
import LeanSMILES.MetaPrograms.Test

/-! Tests for Tanimoto similarity of Morgan fingerprints. -/

open Chem Chem.Exec

def fp (s : String) : MorganFingerprint 2048 :=
  ((molFromSmiles s).toOption.getD default).morganFingerprint 2 2048

#eval tanimoto (fp "CCO") (fp "CCCO")

#test tanimoto (fp "c1ccccc1") (fp "c1ccccc1") == 1.0
#test tanimoto (fp "CCO") (fp "OCC") == 1.0
#test tanimoto (fp "CCO") (fp "CCCO") == tanimoto (fp "CCCO") (fp "CCO")
#test tanimoto (fp "CCO") (fp "c1ccccc1") < 0.2
-- toluene is closer to benzene than ethanol is
#test tanimoto (fp "Cc1ccccc1") (fp "c1ccccc1") > tanimoto (fp "CCO") (fp "c1ccccc1")
#test let t := tanimoto (fp "CC(=O)Oc1ccccc1C(=O)O") (fp "OC(=O)c1ccccc1O")
  0 < t && t < 1
#test (MorganFingerprint.tanimoto (α := Float) ⟨Vector.replicate 8 false⟩ ⟨Vector.replicate 8 false⟩) == 1.0
