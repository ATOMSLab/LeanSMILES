import LeanSMILES.SMILES.Canon
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# LeanSMILES.Tests.Oracle

The parser and canonicalizer against RDKit on the 1 128 Delaney molecules.

`datasets/delaney-oracle.csv` (from `tools/rdkit_oracle.py` on the
`canonical-smiles` branch) records, for each molecule, what RDKit built from
the same string: atom and bond counts, element symbols in input order, total
hydrogen counts, the bond list `i-j:t` (`t` = 1/2/3/12), and RDKit's
canonical SMILES without stereo.

**Syntax, which must match:** atom count, bond count, element symbols and
bond connectivity are properties of the string, so they must agree exactly.

**Semantics, reported for information:** bond types and hydrogen counts are
RDKit's *after* aromaticity perception and the nitro rewrite, which this
library does not do, so they will differ on some molecules by design.

**Canonicity, which must hold:** the canonical SMILES of a molecule must not
change when the molecule is reparsed from it (round trip), nor when its atoms
are relabelled (`finRotate`, `Fin.revPerm`) before canonicalizing.  Agreement
with RDKit's canonical *string* is reported for information only — it is a
different walk and a different tie-breaking rule.

```
lake exe oracle-test [datasets/delaney-oracle.csv]
```
-/

open LeanSMILES LeanSMILES.SMILES

structure Row where
  smiles : String
  rdkitCanon : String
  numAtoms : ℕ
  numBonds : ℕ
  symbols : List String
  totalHs : List ℕ
  /-- `(i, j, t)` with `i < j`. -/
  bonds : List (ℕ × ℕ × ℕ)

def parseNat (s : String) : ℕ := s.trimAscii.toString.toNat?.getD 0

def parseBond (s : String) : ℕ × ℕ × ℕ :=
  match s.splitOn "-" with
  | [i, rest] =>
    match rest.splitOn ":" with
    | [j, t] => (parseNat i, parseNat j, parseNat t)
    | _ => (0, 0, 0)
  | _ => (0, 0, 0)

def parseRow (line : String) : Option Row :=
  match line.splitOn "," with
  | [_, smiles, _, _, _, na, nb, syms, hs, _, _, bonds, _, canon] =>
    some { smiles := smiles.trimAscii.toString, rdkitCanon := canon.trimAscii.toString
           numAtoms := parseNat na, numBonds := parseNat nb
           symbols := (syms.splitOn " ").filter (· ≠ "")
           totalHs := ((hs.splitOn " ").filter (· ≠ "")).map parseNat
           bonds := ((bonds.splitOn " ").filter (· ≠ "")).map parseBond }
  | _ => none

def rdkitType : BondKind → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3
  | .quadruple => 4
  | .aromatic => 12

def sortTriples (l : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  l.mergeSort fun a b => decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.1 ≤ b.2.1))

def main (args : List String) : IO UInt32 := do
  let path := args.headD "datasets/delaney-oracle.csv"
  let lines ← IO.FS.lines path
  let rows := (lines.toList.drop 1).filterMap parseRow
  let mut parsed := 0
  let mut syntaxOk := 0
  let mut bondTypesOk := 0
  let mut hydrogensOk := 0
  let mut roundTrip := 0
  let mut invariant := 0
  let mut sameAsRdkit := 0
  let mut failures : Array String := #[]
  for row in rows do
    match parse row.smiles with
    | .error e => failures := failures.push s!"parse error on {row.smiles}: {e}"
    | .ok M =>
      parsed := parsed + 1
      let m := M.mol
      let symbols := (List.finRange M.n).map fun i =>
        ((m.atom i).element.map Element.symbol).getD "*"
      let mine := sortTriples <| m.bonds.map fun b =>
        (min b.src.val b.dst.val, max b.src.val b.dst.val, rdkitType b.kind)
      let theirs := sortTriples row.bonds
      let connectivity := mine.map (fun t => (t.1, t.2.1)) == theirs.map (fun t => (t.1, t.2.1))
      if M.n == row.numAtoms && m.numBonds == row.numBonds && symbols == row.symbols
          && connectivity then
        syntaxOk := syntaxOk + 1
      else
        failures := failures.push s!"graph differs from RDKit on {row.smiles}"
      if mine == theirs then bondTypesOk := bondTypesOk + 1
      if ((List.finRange M.n).map fun i => (m.atom i).totalH) == row.totalHs then
        hydrogensOk := hydrogensOk + 1
      -- canonicity
      let c := M.canonicalSmiles
      match parse c with
      | .ok M' =>
        if M'.canonicalSmiles == c then roundTrip := roundTrip + 1
        else
          failures := failures.push
            s!"round trip changed {row.smiles}: {c} → {M'.canonicalSmiles}"
      | .error e =>
        failures := failures.push s!"canonical SMILES {c} of {row.smiles} does not parse: {e}"
      let c₁ := (M.relabel (finRotate M.n)).canonicalSmiles
      let c₂ := (M.relabel Fin.revPerm).canonicalSmiles
      if c₁ == c && c₂ == c then invariant := invariant + 1
      else
        failures := failures.push s!"relabelling changed {row.smiles}: {c} / {c₁} / {c₂}"
      if c == row.rdkitCanon then sameAsRdkit := sameAsRdkit + 1
  let line (label : String) (k : ℕ) (tag : String) : String :=
    s!"{label}: {k}/{parsed}  [{tag}]"
  IO.println s!"{rows.length} molecules, {parsed} parsed"
  IO.println (line "syntax (atoms, bonds, symbols, connectivity) = RDKit" syntaxOk "must be all")
  IO.println (line "canonical SMILES survives reparse" roundTrip "must be all")
  IO.println (line "canonical SMILES invariant under relabelling" invariant "must be all")
  IO.println (line "bond types = RDKit (after its aromaticity model)" bondTypesOk "info")
  IO.println (line "hydrogen counts = RDKit (after its sanitization)" hydrogensOk "info")
  IO.println (line "canonical string = RDKit's string" sameAsRdkit "info")
  for f in failures.toList.take 20 do
    IO.println s!"  {f}"
  let ok := parsed == rows.length && syntaxOk == parsed
    && roundTrip == parsed && invariant == parsed
  return if ok then 0 else 1
