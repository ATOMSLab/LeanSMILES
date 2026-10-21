import LeanSMILES.Fingerprint.Morgan

/-!
# Morgan fingerprint test

For every molecule in an oracle file (from `tools/rdkit_oracle.py`), compute the
Morgan fingerprint (radius 2, 2048 bits) in Lean and compare with RDKit's, both
the folded on-bits (`morgan_bits`) and the unfolded identifiers with counts
(`morgan_ids`). Run from the repository root:

    lake exe morgan-test                     # Delaney, as written and in Kekulé form
    lake exe morgan-test datasets/aromaticity-cases-oracle.csv
-/

open Chem

def checkFile (path : String) : IO Bool := do
  let lines := (← IO.FS.lines path).toList.drop 1
  let mut ok := 0
  let mut bad : Array String := #[]
  for line in lines do
    let c := (line.splitOn ",").toArray
    if c.size < 5 then continue
    match molFromSmiles c[1]! with
    | .error e => bad := bad.push s!"row {c[0]!} {c[1]!}: {e}"
    | .ok m =>
      let bits := " ".intercalate (m.morganBits.map toString)
      let ids := " ".intercalate (m.morganIds.map fun (id, n) => s!"{id}:{n}")
      if bits == c[3]! && ids == c[4]! then ok := ok + 1
      else bad := bad.push s!"row {c[0]!} {c[1]!}\n    bits lean  {bits}\n    bits rdkit {c[3]!}"
  IO.println s!"{path}: {ok} / {lines.length} Morgan fingerprints match RDKit"
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
