import LeanSMILES.Canonical.Sanitize

/-!
# Validity test: does Lean accept exactly what RDKit accepts?

Reads lines `1|0 <TAB> SMILES` (RDKit's verdict, from `tools/rdkit_fuzz.py`) and
compares with `Chem.molFromSmiles`. Molecules with elements we do not support
are counted separately. Run from the repository root:

    lake exe canonical-validity-test                      # datasets/fuzz-validity.tsv
    lake exe canonical-validity-test other-file.tsv
-/

open Chem

def main (args : List String) : IO UInt32 := do
  let path := args.headD "datasets/fuzz-validity.tsv"
  let lines ← IO.FS.lines path
  let mut agree := 0
  let mut unsupported := 0
  let mut leanOnly : Array String := #[]
  let mut rdkitOnly : Array String := #[]
  for line in lines do
    let some (verdict, smiles) := (match line.splitOn "\t" with
      | [v, s] => some (v == "1", s) | _ => none) | continue
    match molFromSmiles smiles with
    | .ok _ =>
      if verdict then agree := agree + 1 else leanOnly := leanOnly.push smiles
    | .error e =>
      if !verdict then agree := agree + 1
      else if e.startsWith "unsupported element" then unsupported := unsupported + 1
      else rdkitOnly := rdkitOnly.push s!"{smiles}   ({e})"
  IO.println s!"{path}: agree on {agree} / {lines.size}"
  IO.println s!"  RDKit accepts, Lean rejects (unsupported element): {unsupported}"
  IO.println s!"  Lean accepts, RDKit rejects: {leanOnly.size}"
  for s in leanOnly.toList.take 10 do IO.println s!"    {s}"
  IO.println s!"  RDKit accepts, Lean rejects (other): {rdkitOnly.size}"
  for s in rdkitOnly.toList.take 10 do IO.println s!"    {s}"
  return if leanOnly.isEmpty && rdkitOnly.isEmpty then 0 else 1
