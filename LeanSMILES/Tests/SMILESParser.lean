import LeanSMILES.SMILES.DEFINITIONS
import LeanSMILES.MetaPrograms.Test

/-! Tests for `SMILES.parse`, `Molecule.toSMILES` and hydrogen counting. -/

open Chem

def roundTrip (s : String) : String :=
  match (SMILES.mk s).parse with
  | .ok m => m.toSMILES.str
  | .error e => s!"error: {e}"

def parseError (s : String) : String :=
  match (SMILES.mk s).parse with
  | .ok _ => "ok"
  | .error e => e

def mol! (s : String) : Molecule := ((SMILES.mk s).parse).toOption.getD default

-- round trips (stereo marks are dropped)
#test roundTrip "CCO" == "CCO"
#test roundTrip "CC(=O)O" == "CC(=O)O"
#test roundTrip "c1ccccc1" == "c1ccccc1"
#test roundTrip "C1CC2CCC1C2" == "C1CC2CCC1C2"
#test roundTrip "[NH4+]" == "[NH4+]"
#test roundTrip "[13CH4]" == "[13CH4]"
#test roundTrip "[Na+].[Cl-]" == "[Na+].[Cl-]"
#test roundTrip "c1cc[nH]c1" == "c1cc[nH]c1"
#test roundTrip "C%10CC%10" == "C1CC1"
#test roundTrip "F/C=C/F" == "FC=CF"
#test roundTrip "[CH4]" == "C"
#test roundTrip "C#N" == "C#N"

-- atom and bond counts
#test (mol! "CC(=O)O").atoms.size == 4 && (mol! "CC(=O)O").bonds.size == 3
#test (mol! "c1ccccc1").bonds.size == 6
#test (mol! "c1ccccc1").bonds.all (·.order == .aromatic)
#test (mol! "c1ccccc1-c1ccccc1").bonds.toList.count ⟨5, 6, .single⟩ == 1

-- implicit hydrogens from normal valences
#test (List.range 3).map (mol! "CCO").totalH == [3, 2, 1]
#test (mol! "C=O").totalH 0 == 2
#test (mol! "c1ccccc1").totalH 0 == 1
#test (mol! "c1ccncc1").totalH 3 == 0
#test (mol! "c1cc[nH]c1").totalH 3 == 1
#test (mol! "CS(=O)(=O)C").totalH 1 == 0

-- every parse is well-formed
#test ["CCO", "c1ccccc1", "C1CC2CCC1C2", "[Na+].[Cl-]"].all fun s => decide (mol! s).WellFormed

-- errors
#test parseError "C1CC" == "unclosed ring"
#test parseError "C(C" == "unclosed branch"
#test parseError "C)" == "unmatched ')'"
#test parseError "[Xx]" == "unknown element 'X'"
#test parseError "C==C" == "two consecutive bond symbols"
#test parseError "[C" == "unclosed '['"
#test parseError "=C" == "bond symbol without a preceding atom"
