/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.Perceive
public import LeanSMILES.Fingerprint.Morgan
public import LeanSMILES.Tests.OracleRow

/-!
# Aromaticity test: `Molecule.aromatize` against RDKit

For every molecule of an oracle file (`tools/rdkit_oracle.py`), parse, run
`Molecule.aromatize`, and compare with RDKit's sanitized molecule: bond types,
hydrogen counts, and the Morgan fingerprint computed on the result.

`aromatize` is RDKit's kekulization, aromaticity perception and final
hydrogen counts. It leaves out `cleanUp` (`N(=O)=O` → `[N+](=O)[O-]`) and the
removal of hydrogens written as atoms (`[H]`), so molecules those touch are
counted separately and expected to differ.

    lake exe aromaticity-test [oracle.csv ...]

Defaults to every oracle file, each as written and in Kekulé form: Delaney,
the 56 hand-picked aromaticity cases, the isotope cases and the hydrogen cases.
-/

open LeanSMILES LeanSMILES.Tests

/-- Molecules `aromatize` is not meant to match: RDKit's `cleanUp` rewrites a
neutral 5-valent N (nitro, N-oxide, azide) and a neutral P or halogen with a
double bond to O, and RDKit removes `[H]` atoms. -/
def outOfScope (M : Mol) : Bool :=
  (List.finRange M.n).any fun i ↦
    let a := M.mol.atom i
    a.element == some .H ||
      (a.element == some .N && a.charge == 0 && M.mol.bondOrderSum i + a.totalH ≥ 5) ||
      ((a.element == some .P || a.element == some .Cl || a.element == some .Br ||
          a.element == some .I) && a.charge == 0 &&
        (M.mol.bondsAt i).any fun b ↦
          b.kind == .double && (M.mol.atom (b.other i)).element == some .O &&
            (M.mol.atom (b.other i)).charge == 0)

def check (path : String) : IO Bool := do
  let rows ← readRows path
  let mut parsed := 0
  let mut failed := 0
  let mut scope := 0
  let mut bondsOk := 0
  let mut hsOk := 0
  let mut fpOk := 0
  let mut outside := 0
  let mut outsideFp := 0
  let mut misses : Array String := #[]
  for row in rows do
    match SMILES.parse row.smiles with
    | .error _ => pure ()
    | .ok M0 =>
      parsed := parsed + 1
      match M0.aromatize with
      | .error e =>
        failed := failed + 1
        misses := misses.push s!"aromatize failed on {row.smiles}: {e}"
      | .ok M =>
        let fp := " ".intercalate (M.morganBits.map toString) == row.morganBits &&
          " ".intercalate (M.morganIds.map fun (id, c) ↦ s!"{id}:{c}") == row.morganIds
        if outOfScope M0 then
          outside := outside + 1
          if fp then outsideFp := outsideFp + 1
        else
          scope := scope + 1
          let b := bondTypesAgree row M
          let h := hydrogensAgree row M
          if b then bondsOk := bondsOk + 1
          if h then hsOk := hsOk + 1
          if fp then fpOk := fpOk + 1
          if !(b && h && fp) then
            misses := misses.push
              s!"{row.smiles}: bonds {b}, hydrogens {h}, fingerprint {fp}"
  IO.println s!"{path}: {rows.length} molecules, {parsed} parsed, aromatize failed on {failed}"
  IO.println s!"  in scope {scope}: bond types = RDKit {bondsOk}, hydrogens = RDKit {hsOk}, \
    fingerprint = RDKit {fpOk}  [must be all]"
  IO.println
    s!"  touched by cleanUp or [H] removal {outside}: fingerprint = RDKit {outsideFp}  [info]"
  for f in misses.toList.take 8 do
    IO.println s!"    {f}"
  return failed == 0 && bondsOk == scope && hsOk == scope && fpOk == scope

/-- On `datasets/fuzz-validity.tsv`, `aromatize` must never fail on a string
RDKit accepts; how many of RDKit's rejections it reproduces (kekulization
failures) is reported. -/
def checkFuzz (path : String) : IO Bool := do
  let mut wrong : Array String := #[]
  let mut caught := 0
  let mut rejected := 0
  for line in (← IO.FS.lines path).toList do
    match line.splitOn "\t" with
    | [verdict, s] =>
      if let .ok M := SMILES.parse s then
        let ok := (M.aromatize).toBool
        if verdict == "1" && !ok then wrong := wrong.push s
        if verdict == "0" then
          rejected := rejected + 1
          if !ok then caught := caught + 1
    | _ => pure ()
  IO.println s!"{path}: RDKit accepts, aromatize fails: {wrong.size}  [must be 0]"
  IO.println s!"  RDKit rejects and Lean parses {rejected}: aromatize fails on {caught}  [info]"
  for s in wrong.toList.take 8 do
    IO.println s!"    {s}"
  return wrong.isEmpty

public def main (args : List String) : IO UInt32 := do
  let paths := if args.isEmpty then
      ["datasets/delaney-oracle.csv", "datasets/delaney-kekule-oracle.csv",
       "datasets/aromaticity-cases-oracle.csv", "datasets/aromaticity-cases-kekule-oracle.csv",
       "datasets/isotope-cases-oracle.csv", "datasets/isotope-cases-kekule-oracle.csv",
       "datasets/hydrogen-cases-oracle.csv", "datasets/hydrogen-cases-kekule-oracle.csv"]
    else args
  let mut ok := true
  for p in paths do
    if !(← check p) then ok := false
  if args.isEmpty then
    if !(← checkFuzz "datasets/fuzz-validity.tsv") then ok := false
  return if ok then 0 else 1
