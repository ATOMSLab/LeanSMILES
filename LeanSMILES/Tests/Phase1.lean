import LeanSMILES.Canonical.Sanitize

/-!
# Phase 1 test: molecular graph vs RDKit

Parses every SMILES in an oracle file and compares, atom by atom and bond by
bond, with RDKit: atom and bond counts, element symbols, total H counts, formal
charges, ring membership and bond types. Run from the repository root:

    lake exe phase1-test                                    # both oracle files
    lake exe phase1-test datasets/delaney-kekule-oracle.csv # one file
-/

open Chem

/-- What we compute for one molecule, in the oracle's column format. -/
structure Summary where
  numAtoms : Nat
  numBonds : Nat
  symbols : String
  totalHs : String
  charges : String
  inRing : String
  bonds : String
  deriving BEq

def summarize (m : Mol) : Summary :=
  let idx := List.range m.numAtoms
  let join (f : Nat → String) := " ".intercalate (idx.map f)
  let bonds := m.bonds.toList.map fun b =>
    s!"{min b.src b.dst}-{max b.src b.dst}:{b.order.rdkitType}"
  { numAtoms := m.numAtoms, numBonds := m.numBonds,
    symbols := join fun i => symbol m.atoms[i]!.atomicNum,
    totalHs := join fun i => toString (m.totalHs i),
    charges := join fun i => toString m.atoms[i]!.charge,
    inRing := join fun i => if m.atomInRing i then "1" else "0",
    bonds := " ".intercalate (bonds.mergeSort (· < ·)) }

/-- Names of the fields where `ours` and `rdkit` differ. -/
def diffs (ours rdkit : Summary) : List String :=
  [("num_atoms", ours.numAtoms == rdkit.numAtoms), ("num_bonds", ours.numBonds == rdkit.numBonds),
   ("atom_symbols", ours.symbols == rdkit.symbols), ("atom_total_hs", ours.totalHs == rdkit.totalHs),
   ("atom_charges", ours.charges == rdkit.charges), ("atom_in_ring", ours.inRing == rdkit.inRing),
   ("bonds", ours.bonds == rdkit.bonds)]
  |>.filterMap fun (name, ok) => if ok then none else some name

/-- Check every molecule in one oracle file; returns true if all in-scope rows match. -/
def checkFile (path : String) : IO Bool := do
  IO.println s!"== {path}"
  let lines := (← IO.FS.lines path).toList.drop 1
  let mut total := 0
  let mut passed := 0
  let mut easyTotal := 0
  let mut easyPassed := 0
  let mut failures : Array String := #[]
  for line in lines do
    if line.trimAscii.isEmpty then continue
    let c := (line.splitOn ",").toArray
    let rdkit : Summary :=
      { numAtoms := c[5]!.toNat!, numBonds := c[6]!.toNat!, symbols := c[7]!,
        totalHs := c[8]!, charges := c[9]!, inRing := c[10]!, bonds := c[11]! }
    let easy := c[12]! == "0"
    total := total + 1
    if easy then easyTotal := easyTotal + 1
    match molFromSmiles c[1]! with
    | .error e => failures := failures.push s!"row {c[0]!} {c[1]!}: parse error: {e}"
    | .ok m =>
      let bad := diffs (summarize m) rdkit
      if bad.isEmpty then
        passed := passed + 1
        if easy then easyPassed := easyPassed + 1
      else
        let ours := summarize m
        let detail := bad.map fun
          | "atom_total_hs" => s!"\n    H ours  {ours.totalHs}\n    H rdkit {rdkit.totalHs}"
          | "atom_charges" => s!"\n    q ours  {ours.charges}\n    q rdkit {rdkit.charges}"
          | "atom_in_ring" => s!"\n    ring ours  {ours.inRing}\n    ring rdkit {rdkit.inRing}"
          | "bonds" => s!"\n    bonds ours  {ours.bonds}\n    bonds rdkit {rdkit.bonds}"
          | other => s!" {other}"
        failures := failures.push s!"row {c[0]!} {c[1]!}:{String.join detail}"
  IO.println s!"all molecules:            {passed} / {total} match RDKit"
  IO.println s!"needs_aromaticity = 0:    {easyPassed} / {easyTotal} match RDKit"
  for f in failures.toList.take 8 do IO.println f
  if failures.size > 8 then IO.println s!"... and {failures.size - 8} more"
  return passed == total

def main (args : List String) : IO UInt32 := do
  let files := if args.isEmpty
    then ["datasets/delaney-oracle.csv", "datasets/delaney-kekule-oracle.csv"] else args
  let mut ok := true
  for f in files do
    ok := (← checkFile f) && ok
  return if ok then 0 else 1
