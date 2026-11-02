/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.SMILES.Canon

/-!
# LeanSMILES.Tests.OracleRow

Shared reading of `datasets/*-oracle.csv` (from `tools/rdkit_oracle.py` on the
`canonical-smiles` branch): one row per molecule, RDKit's answers in columns.

```
index, smiles, canonical_smiles, morgan_bits, morgan_ids, num_atoms, num_bonds,
atom_symbols, atom_total_hs, atom_charges, atom_in_ring, bonds,
needs_aromaticity, canonical_smiles_nostereo
```

Multi-value columns are space-separated; `bonds` entries are `i-j:t` with
`i < j` and `t` RDKit's bond type (1/2/3/12); `morgan_ids` entries are
`id:count`.  Atom order is the SMILES order, which this library keeps too.
-/

@[expose] public section

namespace LeanSMILES.Tests

open LeanSMILES

/-- One oracle CSV row: RDKit's answers for one molecule, as `parseRow` reads them. The
per-atom lists are in SMILES order; the columns not needed by any test are not kept. -/
structure Row where
  /-- The `smiles` column: the input SMILES as the dataset writes it. -/
  smiles : String
  /-- The `canonical_smiles_nostereo` column: RDKit's canonical SMILES with stereo dropped. -/
  rdkitCanon : String
  /-- The raw `morgan_bits` column: the set bits of the Morgan fingerprint, space-separated. -/
  morganBits : String
  /-- The raw `morgan_ids` column: `id:count` entries of the Morgan invariants, space-separated. -/
  morganIds : String
  /-- The `num_atoms` column: RDKit's heavy-atom count. -/
  numAtoms : ℕ
  /-- The `num_bonds` column: RDKit's bond count. -/
  numBonds : ℕ
  /-- The `atom_symbols` column: one element symbol per atom. -/
  symbols : List String
  /-- The `atom_total_hs` column: the total hydrogen count of each atom. -/
  totalHs : List ℕ
  /-- The `atom_in_ring` column: `1` for an atom in a ring, `0` otherwise. -/
  inRing : List ℕ
  /-- The `bonds` column parsed to `(i, j, t)` with `i < j` and `t` RDKit's bond type number. -/
  bonds : List (ℕ × ℕ × ℕ)

/-- A numeric column as a `ℕ`, ignoring surrounding whitespace; `0` if it is not a number. -/
def parseNat (s : String) : ℕ := s.trimAscii.toString.toNat?.getD 0

/-- The entries of a space-separated multi-value column, empty entries dropped. -/
def spaceList (s : String) : List String := (s.splitOn " ").filter (· ≠ "")

/-- One `bonds` entry `i-j:t` as `(i, j, t)`; `(0, 0, 0)` if it does not have that shape. -/
def parseBond (s : String) : ℕ × ℕ × ℕ :=
  match s.splitOn "-" with
  | [i, rest] =>
    match rest.splitOn ":" with
    | [j, t] => (parseNat i, parseNat j, parseNat t)
    | _ => (0, 0, 0)
  | _ => (0, 0, 0)

/-- A data line of an oracle file as a `Row`, by column position (`none` unless it has all 14
columns); `canonical_smiles`, `atom_charges` and `needs_aromaticity` are skipped. -/
def parseRow (line : String) : Option Row :=
  match line.splitOn "," with
  | [_, smiles, _, mbits, mids, na, nb, syms, hs, _, ring, bonds, _, canon] =>
    some { smiles := smiles.trimAscii.toString, rdkitCanon := canon.trimAscii.toString
           morganBits := mbits.trimAscii.toString, morganIds := mids.trimAscii.toString
           numAtoms := parseNat na, numBonds := parseNat nb
           symbols := spaceList syms
           totalHs := (spaceList hs).map parseNat
           inRing := (spaceList ring).map parseNat
           bonds := (spaceList bonds).map parseBond }
  | _ => none

/-- All rows of an oracle file. -/
def readRows (path : String) : IO (List Row) := do
  let lines ← IO.FS.lines path
  return (lines.toList.drop 1).filterMap parseRow

/-- RDKit's `Chem.BondType` number, as the oracle writes it. -/
def rdkitType : BondKind → ℕ
  | .single => 1
  | .double => 2
  | .triple => 3
  | .quadruple => 4
  | .aromatic => 12

/-- `(i, j, t)` triples sorted by `i`, then `j`, so that two bond lists compare entrywise. -/
def sortTriples (l : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  l.mergeSort fun a b ↦ decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.1 ≤ b.2.1))

/-- The molecule's bonds as sorted `(i, j, t)` triples, `i < j`. -/
def bondTriples (M : Mol) : List (ℕ × ℕ × ℕ) :=
  sortTriples <| M.mol.bonds.map fun b ↦
    (min b.src.val b.dst.val, max b.src.val b.dst.val, rdkitType b.kind)

/-- The element symbol of each atom of `M` in SMILES order, `*` for a wildcard atom; the
library's answer to the `atom_symbols` column. -/
def symbolsOf (M : Mol) : List String :=
  (List.finRange M.n).map fun i ↦ ((M.mol.atom i).element.map Element.symbol).getD "*"

/-- The total hydrogen count of each atom of `M` in SMILES order; the library's answer to the
`atom_total_hs` column. -/
def totalHsOf (M : Mol) : List ℕ := (List.finRange M.n).map fun i ↦ (M.mol.atom i).totalH

/-- Same atoms, same bonds between the same atoms (syntax). -/
def connectivityAgrees (row : Row) (M : Mol) : Bool :=
  M.n == row.numAtoms && M.mol.numBonds == row.numBonds && symbolsOf M == row.symbols
    && (bondTriples M).map (fun t ↦ (t.1, t.2.1))
      == (sortTriples row.bonds).map (fun t ↦ (t.1, t.2.1))

/-- The as-written bond types equal RDKit's after its aromaticity model. -/
def bondTypesAgree (row : Row) (M : Mol) : Bool := bondTriples M == sortTriples row.bonds

/-- The default-valence hydrogen counts equal RDKit's after its sanitization. -/
def hydrogensAgree (row : Row) (M : Mol) : Bool := totalHsOf M == row.totalHs

end LeanSMILES.Tests
