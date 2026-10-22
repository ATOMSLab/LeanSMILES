/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Fingerprint.Morgan
public import LeanSMILES.Tests.OracleRow
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# LeanSMILES.Tests.Morgan

Morgan fingerprints against RDKit on the 1 128 Delaney molecules
(`datasets/delaney-oracle.csv`: columns `morgan_bits`, `morgan_ids`,
`atom_in_ring`).

This library fingerprints the graph *as written*, RDKit the graph *after
sanitization* (aromaticity perception, nitro rewrite), so the two can only
agree where those graphs agree.  Hence three kinds of check:

* **Ring membership must match on every molecule** — it is pure graph theory.
* **Conditioned on graph agreement, the fingerprint must match**: on every
  molecule whose as-written bond types and hydrogen counts equal RDKit's, the
  unfolded identifiers with counts, and the folded bits, must be identical.
  A miss there is a bug in the port.
* **Relabeling invariance must hold on every molecule**: the identifiers are
  unchanged when the atoms are renumbered (`finRotate`, `Fin.revPerm`).

Overall agreement with RDKit is reported for information.

```
lake exe morgan-test [datasets/delaney-oracle.csv]
```
-/

open LeanSMILES LeanSMILES.SMILES LeanSMILES.Tests

def bitsString (M : Mol) : String := " ".intercalate (M.morganBits.map toString)

def idsString (M : Mol) : String :=
  " ".intercalate (M.morganIds.map fun (id, c) ↦ s!"{id}:{c}")

def inRingList (M : Mol) : List ℕ := M.mol.inRingVector.toList.map fun b ↦ if b then 1 else 0

public def main (args : List String) : IO UInt32 := do
  let path := args.headD "datasets/delaney-oracle.csv"
  let rows ← readRows path
  let mut parsed := 0
  let mut ringOk := 0
  let mut graphOk := 0
  let mut graphOkFpOk := 0
  let mut bitsOk := 0
  let mut idsOk := 0
  let mut invariant := 0
  let mut failures : Array String := #[]
  let mut skipped : Array String := #[]
  for row in rows do
    match parse row.smiles with
    | .error e =>
      if e.isGrammarDeviation then skipped := skipped.push s!"{row.smiles}: {e}"
      else failures := failures.push s!"parse error on {row.smiles}: {e}"
    | .ok M =>
      parsed := parsed + 1
      if inRingList M == row.inRing then ringOk := ringOk + 1
      else failures := failures.push s!"ring membership differs from RDKit on {row.smiles}"
      let ids := idsString M
      let bits := bitsString M
      let fpOk := ids == row.morganIds && bits == row.morganBits
      if bits == row.morganBits then bitsOk := bitsOk + 1
      if ids == row.morganIds then idsOk := idsOk + 1
      if bondTypesAgree row M && hydrogensAgree row M then
        graphOk := graphOk + 1
        if fpOk then graphOkFpOk := graphOkFpOk + 1
        else
          failures := failures.push
            s!"graph = RDKit's but fingerprint differs on {row.smiles}\n    lean  {bits}\n    \
              rdkit {row.morganBits}"
      let ids₁ := (M.relabel (finRotate M.n)).morganIds
      let ids₂ := (M.relabel Fin.revPerm).morganIds
      if ids₁ == M.morganIds && ids₂ == M.morganIds then invariant := invariant + 1
      else failures := failures.push s!"relabeling changed the fingerprint of {row.smiles}"
  IO.println s!"{rows.length} molecules, {parsed} parsed, \
    {skipped.size} rejected by the OpenSMILES grammar (deliberate)"
  for f in skipped.toList do
    IO.println s!"  {f}"
  IO.println s!"ring membership = RDKit: {ringOk}/{parsed}  [must be all]"
  IO.println
    s!"fingerprint = RDKit where the graph = RDKit's: {graphOkFpOk}/{graphOk}  [must be all]"
  IO.println s!"fingerprint invariant under relabeling: {invariant}/{parsed}  [must be all]"
  IO.println s!"on-bits = RDKit overall: {bitsOk}/{parsed}  [info: graph as written]"
  IO.println s!"identifiers+counts = RDKit overall: {idsOk}/{parsed}  [info: graph as written]"
  for f in failures.toList.take 10 do
    IO.println s!"  {f}"
  let ok := parsed + skipped.size == rows.length && ringOk == parsed
    && graphOkFpOk == graphOk && invariant == parsed
  return if ok then 0 else 1
