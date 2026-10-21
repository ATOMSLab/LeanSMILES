import LeanSMILES.Canonical

/-!
# Canonical SMILES test

For every molecule in an oracle file (from `tools/rdkit_oracle.py`), convert its
SMILES with `Chem.canonicalSmiles` and compare with RDKit's
`MolToSmiles(mol, isomericSmiles=False)` (column `canonical_smiles_nostereo`).
Run from the repository root:

    lake exe canonical-test                     # Delaney, as written and in Kekulé form
    lake exe canonical-test datasets/aromaticity-cases-oracle.csv
-/

open Chem

def checkFile (path : String) : IO Bool := do
  let lines := (← IO.FS.lines path).toList.drop 1
  let mut ok := 0
  let mut bad : Array String := #[]
  for line in lines do
    let c := (line.splitOn ",").toArray
    if c.size < 14 then continue
    match canonicalSmiles c[1]! with
    | .ok got =>
      if got == c[13]! then ok := ok + 1
      else bad := bad.push s!"row {c[0]!} {c[1]!}\n    lean  {got}\n    rdkit {c[13]!}"
    | .error e => bad := bad.push s!"row {c[0]!} {c[1]!}\n    lean error: {e}"
  IO.println s!"{path}: {ok} / {lines.length} canonical SMILES match RDKit"
  for b in bad.toList.take 8 do IO.println s!"  {b}"
  if bad.size > 8 then IO.println s!"  ... and {bad.size - 8} more"
  return bad.isEmpty

def main (args : List String) : IO UInt32 := do
  let files := if args.isEmpty
    then ["datasets/delaney-oracle.csv", "datasets/delaney-kekule-oracle.csv"] else args
  let mut allOk := true
  for f in files do
    allOk := (← checkFile f) && allOk
  return if allOk then 0 else 1
