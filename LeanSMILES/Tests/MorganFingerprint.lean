import LeanSMILES.SMILES.Definitions
import LeanSMILES.MetaPrograms.Test

/-! Tests for `Molecule.morganFingerprint` and its helpers. -/

open Chem

def fp (s : String) (radius : Nat := 2) : MorganFingerprint 2048 :=
  ((SMILES.mk s).morganFingerprint radius 2048).toOption.getD ⟨Vector.replicate 2048 false⟩

def mol! (s : String) : Molecule := ((SMILES.mk s).parse).toOption.getD default

-- independent of how the SMILES is written
#test fp "CCO" == fp "OCC"
#test fp "Oc1ccccc1C" == fp "Cc1ccccc1O"
#test fp "c1ccccc1" == fp "c1ccc(cc1)"
-- distinguishes isomers
#test fp "CCO" != fp "COC"
-- methane: one environment per radius
#test (fp "C").popCount == 3
-- benzene: all six atoms are equivalent at every radius
#test (fp "c1ccccc1").popCount == 3
-- radius 0 sets at most one bit per distinct atom type
#test (fp "CCO" 0).popCount == 3
#test (fp "CCO" 0).popCount ≤ (fp "CCO" 2).popCount

-- ring membership
#test (List.range 6).all (mol! "C1CCCCC1").atomInRing
#test !(mol! "CCCCCC").atomInRing 0
#test (List.range 4).map (mol! "CC1CC1").atomInRing == [false, true, true, true]

-- hashing is deterministic
#test fnv [1, 2, 3] == fnv [1, 2, 3] && fnv [1, 2, 3] != fnv [3, 2, 1]

-- features
#test ((fp "CCO").toFeatures (α := Float)).toList.foldl (· + ·) 0 == 9.0
