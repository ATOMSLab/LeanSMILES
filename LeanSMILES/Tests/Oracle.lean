/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Tests.OracleRow
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# LeanSMILES.Tests.Oracle

The parser and canonicalizer against RDKit on the 1 128 Delaney molecules
(`datasets/delaney-oracle.csv`, see `LeanSMILES.Tests.OracleRow`).

**Syntax, which must match:** atom count, bond count, element symbols and
bond connectivity are properties of the string, so they must agree exactly.
A row the parser rejects by a deliberate OpenSMILES rule
(`ParseError.isGrammarDeviation`: a ring-closure label after a branch, as
chlorothalonil's `…c(Cl)1` is written) is listed and left out of the counts.

**Semantics, reported for information:** bond types and hydrogen counts are
RDKit's *after* aromaticity perception and the nitro rewrite, which this
library does not do, so they will differ on some molecules by design.

**Canonicity, which must hold:** the canonical SMILES of a molecule must not
change when the molecule is reparsed from it (round trip), nor when its atoms
are relabeled (`finRotate`, `Fin.revPerm`) before canonicalizing.  Agreement
with RDKit's canonical *string* is reported for information only — it is a
different walk and a different tie-breaking rule.

**Spellings, which must hold:** a handful of molecules written two ways (`spellings`).  Brackets
that repeat what the default-valence rule says (`[CH4]`, `[n]`, `[Cl]`, caffeine as
Sigma-Aldrich writes it) must not change the canonical SMILES; brackets that say something
(`[CH3]`, `[C]`, `[13CH4]`, `[NH4+]`, `[nH]`) must.

```
lake exe oracle-test [datasets/delaney-oracle.csv]
```
-/

open LeanSMILES LeanSMILES.SMILES LeanSMILES.Tests

/-- Pairs of SMILES, and whether they must have the same canonical SMILES. -/
def spellings : List (String × String × Bool) :=
  [ ("C", "[CH4]", true)
  , ("CCO", "[CH3][CH2][OH]", true)
  , ("ClCCl", "[Cl]C[Cl]", true)
  , ("c1ccncc1", "c1cc[n]cc1", true)
  , ("*C", "[*]C", true)
  , ("Cn1cnc2c1c(=O)n(C)c(=O)n2C", "C[n]1cnc2c1c(=O)n(C)c(=O)n2C", true)
  -- caffeine as RCSB and as Sigma-Aldrich write it
  , ("O=C2N(c1ncn(c1C(=O)N2C)C)C", "[n]1(c2c(nc1)N(C(=O)N(C2=O)C)C)C", true)
  , ("C", "[CH3]", false)
  , ("C", "[C]", false)
  , ("C", "[13CH4]", false)
  , ("N", "[NH4+]", false)
  , ("c1cc[nH]c1", "c1ccnc1", false) ]

/-- The `spellings` that fail: a pair that must agree and does not, or must differ and does
not, or whose canonical SMILES does not survive a reparse. -/
def spellingFailures : List String :=
  spellings.filterMap fun (a, b, same) ↦
    match parse a, parse b with
    | .ok A, .ok B =>
      let ca := A.canonicalSmiles
      let cb := B.canonicalSmiles
      let stable (c : String) : Bool := match parse c with
        | .ok C => C.canonicalSmiles == c
        | .error _ => false
      if (ca == cb) != same then
        some s!"{a} and {b} must {if same then "agree" else "differ"}: {ca} vs {cb}"
      else if !(stable ca && stable cb) then
        some s!"canonical SMILES of {a} or {b} changes on reparse: {ca}, {cb}"
      else none
    | _, _ => some s!"{a} or {b} does not parse"

/-- Entry point of `lake exe oracle-test`: runs the checks described above on the CSV named by
the first argument (default `datasets/delaney-oracle.csv`), exiting `0` iff every "must" holds. -/
public def main (args : List String) : IO UInt32 := do
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
  let mut skipped : Array String := #[]
  for row in rows do
    match parse row.smiles with
    | .error e =>
      if e.isGrammarDeviation then skipped := skipped.push s!"{row.smiles}: {e}"
      else failures := failures.push s!"parse error on {row.smiles}: {e}"
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
  IO.println s!"{rows.length} molecules, {parsed} parsed, \
    {skipped.size} rejected by the OpenSMILES grammar (deliberate)"
  for f in skipped.toList do
    IO.println s!"  {f}"
  IO.println (line "syntax (atoms, bonds, symbols, connectivity) = RDKit" syntaxOk "must be all")
  IO.println (line "canonical SMILES survives reparse" roundTrip "must be all")
  IO.println (line "canonical SMILES invariant under relabeling" invariant "must be all")
  IO.println (line "canonicalize.toSmiles = canonical SMILES" canonicalizeOk "must be all")
  IO.println (line "bond types = RDKit (after its aromaticity model)" bondTypesOk "info")
  IO.println (line "hydrogen counts = RDKit (after its sanitization)" hydrogensOk "must be all")
  IO.println (line "canonical string = RDKit's string" sameAsRdkit "info")
  IO.println s!"spellings (redundant brackets dropped, meaningful ones kept): \
    {spellings.length - spellingFailures.length}/{spellings.length}  [must be all]"
  for f in spellingFailures ++ failures.toList.take 20 do
    IO.println s!"  {f}"
  let ok := parsed + skipped.size == rows.length && syntaxOk == parsed
    && roundTrip == parsed && invariant == parsed && canonicalizeOk == parsed
    && hydrogensOk == parsed && spellingFailures.isEmpty
  return if ok then 0 else 1
