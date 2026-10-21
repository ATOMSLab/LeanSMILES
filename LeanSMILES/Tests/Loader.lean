import LeanSMILES.API.Loader
import LeanSMILES.MetaPrograms.Test

/-! Tests for `parseRecords`, `validate` and `clean` on a small inline dataset. -/

open Primitives API

def header := "Compound ID,ESOL predicted log solubility in mols per litre,Minimum Degree,\
  Molecular Weight,Number of H-Bond Donors,Number of Rings,Number of Rotatable Bonds,\
  Polar Surface Area,measured log solubility in mols per litre,smiles\n"

def text := header ++
  "ethanol,0.02,1,46.07,1,0,0,20.23,1.1,CCO\n" ++
  "\"ethanol, again\",0.02,1,46.07,1,0,0,20.23,1.1,OCC \n" ++
  "broken,0,1,1,0,0,0,0,0,C1CC\n" ++
  "benzene,-1.9,2,78.11,0,1,0,0,-1.64,c1ccccc1\n"

def records := (CSV.parse text >>= (parseRecords ·)).toOption.getD #[]

#test records.size == 4
#test records[1]!.compoundId == "ethanol, again"
-- whitespace around SMILES is trimmed
#test records[1]!.smiles.str == "OCC"
#test records[3]!.logS == ⟨-164, -2⟩
#test (records[3]!.descriptors.map Decimal.toFloat).toList == [2.0, 78.11, 0.0, 1.0, 0.0, 0.0]
#test records.map (·.line) == #[2, 3, 4, 5]

def cleaned := clean records

-- the ring that never closes is rejected, the second ethanol is a duplicate
#test cleaned.2.original == 4
#test cleaned.2.invalid.map (·.1) == #[4]
#test cleaned.2.invalid[0]!.2.2 == "unclosed ring"
#test cleaned.2.duplicates == #[(3, "CCO")]
#test cleaned.2.unique == 2 && cleaned.1.size == 2
#test cleaned.1.map (·.compoundId) == #["ethanol", "benzene"]
-- each kept record has a molecule and a canonical SMILES
#test cleaned.1.map (·.canonical.smiles.str) == #["CCO", "c1ccccc1"]
#test cleaned.1.map (·.molecule.atoms.size) == #[3, 6]

-- a non-numeric value is an error that names the line and column
#test (CSV.parse (header ++ "x,abc,1,1,0,0,0,0,0,C\n") >>= (parseRecords ·)).toOption.isNone
-- a missing column is an error
#test (CSV.parse "smiles\nC\n" >>= (parseRecords ·)).toOption.isNone
