import LeanSMILES.Data.CSVparser
import LeanSMILES.Fingerprint.Morgan
open CSVparser Chem

/-!
# Example: Morgan fingerprints

A Morgan fingerprint describes a molecule by the small neighbourhoods around its
atoms (up to `radius` bonds away). Each neighbourhood is hashed to a number and
folded into one of 2048 bits. `morganBits` gives the same on-bits as RDKit's
`GetMorganGenerator(radius=2, fpSize=2048).GetFingerprint(mol)`.

Click on an `#eval` line to see its result in the Infoview.
-/

-- The on-bits of ethanol and benzene (same as RDKit)
#eval morganBits "CCO"            -- [80, 222, 294, 807, 1057, 1410]
#eval morganBits "c1ccccc1"       -- [389, 1088, 1873]

-- Every spelling of a molecule gives the same fingerprint
#eval ["c1ccccc1", "C1=CC=CC=C1"].map morganBits

-- Radius 0 only looks at single atoms; radius 1 adds their neighbours, and so on
#eval (List.range 4).map fun r => (morganBits "CC(=O)Oc1ccccc1C(=O)O" r).map (·.length)

-- The unfolded identifiers (before folding into 2048 bits) with their counts
#eval (molFromSmiles "CCO").map (·.morganIds)

-- Tanimoto similarity: shared bits / bits in either (1 = identical fingerprints)
def similarity (a b : String) : Except String Float := do
  return tanimoto (← morganBits a) (← morganBits b)

#eval similarity "c1ccccc1O" "c1ccccc1O"                  -- phenol vs itself: 1.0
#eval similarity "c1ccccc1O" "Cc1ccccc1O"                 -- phenol vs cresol
#eval similarity "c1ccccc1O" "CCCCCCCC"                   -- phenol vs octane: 0

-- Two EGFR drugs from ENCH 470: gefitinib and erlotinib share the quinazoline core
def gefitinib := "COc1cc2ncnc(Nc3ccc(F)c(Cl)c3)c2cc1OCCCN1CCOCC1"
def erlotinib := "C#Cc1cccc(Nc2ncnc3cc(OCCOC)c(OCCOC)cc23)c1"
#eval similarity gefitinib erlotinib

-- A 2048-long true/false vector, ready to use as ML features
#eval (molFromSmiles "CCO").map fun m => (m.morganVector.toList.filter id).length

-- With the dataset: fingerprints of the first Delaney molecules
def records := load "datasets/delaney-processed.csv"

#eval (List.range 3).map fun i => (records[i].smiles, (morganBits records[i].smiles).map (·.length))

-- Isotopes change the fingerprint by their mass shift int(exact mass − atomic weight):
-- [2H] shifts by 1, but [13C] by 0 (13.0034 − 12.011 truncates to 0), as in RDKit
#eval isotopeMassShift 1 (some 2)     -- 1
#eval isotopeMassShift 6 (some 13)    -- 0
#eval ["C", "[13CH4]", "[2H]C([2H])([2H])[2H]"].map morganBits
