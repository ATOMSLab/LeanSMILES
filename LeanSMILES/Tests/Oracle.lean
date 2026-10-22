/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
import LeanSMILES.Tests.OracleRow
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# LeanSMILES.Tests.Oracle

The parser and canonicalizer against RDKit on the 1 128 Delaney molecules
(`datasets/delaney-oracle.csv`, see `LeanSMILES.Tests.OracleRow`).

**Syntax, which must match:** atom count, bond count, element symbols and
bond connectivity are properties of the string, so they must agree exactly.

**Semantics, reported for information:** bond types and hydrogen counts are
RDKit's *after* aromaticity perception and the nitro rewrite, which this
library does not do, so they will differ on some molecules by design.

**Canonicity, which must hold:** the canonical SMILES of a molecule must not
change when the molecule is reparsed from it (round trip), nor when its atoms
are relabeled (`finRotate`, `Fin.revPerm`) before canonicalizing.  Agreement
with RDKit's canonical *string* is reported for information only — it is a
different walk and a different tie-breaking rule.

```
lake exe oracle-test [datasets/delaney-oracle.csv]
```
-/

open LeanSMILES LeanSMILES.SMILES LeanSMILES.Tests

def main (args : List String) : IO UInt32 := do
  let path := args.headD "datasets/delaney-oracle.csv"
  let rows ← readRows path
  let mut parsed := 0
  let mut syntaxOk := 0
  let mut bondTypesOk := 0
  let mut hydrogensOk := 0
  let mut roundTrip := 0
  let mut invariant := 0
  let mut canonicalizeOk := 0
  let mut sameAsRdkit := 0
  let mut failures : Array String := #[]
  for row in rows do
    match parse row.smiles with
    | .error e => failures := failures.push s!"parse error on {row.smiles}: {e}"
    | .ok M =>
      parsed := parsed + 1
      if connectivityAgrees row M then syntaxOk := syntaxOk + 1
      else failures := failures.push s!"graph differs from RDKit on {row.smiles}"
      if bondTypesAgree row M then bondTypesOk := bondTypesOk + 1
      if hydrogensAgree row M then hydrogensOk := hydrogensOk + 1
      else failures := failures.push s!"hydrogen counts differ from RDKit on {row.smiles}"
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
        failures := failures.push s!"relabeling changed {row.smiles}: {c} / {c₁} / {c₂}"
      -- the relabeled molecule, written in its new atom order, is the canonical string
      let c₃ := M.canonicalize.toSmiles
      if c₃ == c then canonicalizeOk := canonicalizeOk + 1
      else failures := failures.push s!"canonicalize of {row.smiles} writes {c₃}, not {c}"
      if c == row.rdkitCanon then sameAsRdkit := sameAsRdkit + 1
  let line (label : String) (k : ℕ) (tag : String) : String :=
    s!"{label}: {k}/{parsed}  [{tag}]"
  IO.println s!"{rows.length} molecules, {parsed} parsed"
  IO.println (line "syntax (atoms, bonds, symbols, connectivity) = RDKit" syntaxOk "must be all")
  IO.println (line "canonical SMILES survives reparse" roundTrip "must be all")
  IO.println (line "canonical SMILES invariant under relabeling" invariant "must be all")
  IO.println (line "canonicalize.toSmiles = canonical SMILES" canonicalizeOk "must be all")
  IO.println (line "bond types = RDKit (after its aromaticity model)" bondTypesOk "info")
  IO.println (line "hydrogen counts = RDKit (after its sanitization)" hydrogensOk "must be all")
  IO.println (line "canonical string = RDKit's string" sameAsRdkit "info")
  for f in failures.toList.take 20 do
    IO.println s!"  {f}"
  let ok := parsed == rows.length && syntaxOk == parsed
    && roundTrip == parsed && invariant == parsed && canonicalizeOk == parsed
    && hydrogensOk == parsed
  return if ok then 0 else 1
