/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.SMILES.Canon

/-!
# LeanSMILES.Tests.Charge

`Molecule.checkCharges` on hand-picked SMILES.

Every string here must *parse*: the tokenizer accepts any run of `+`/`-`
signs and any number of digits, by design, so `[C+123]` and `[H+++]` are
syntactically fine and `SMILES.parse` stays total over valid syntax.  The
chemistry check must then accept exactly the physically possible charges —
`charge ≤ Z` and `-shellVacancy ≤ charge`, `±15` for `*` — and its message
must name the atom.  Finally, consistency must be unchanged by relabeling and
canonicalization at runtime, as `chargesConsistent_relabel` and
`chargesConsistent_canonicalize` say.

```
lake exe charge-test
```
-/

open LeanSMILES LeanSMILES.SMILES

/-- Must parse and pass `checkCharges`. -/
def consistent : List String :=
  ["C", "CCO", "[Na+]", "[O-2]", "[Fe+3]", "[Fe+++]", "[NH4+]", "[H-]", "[H+]", "[Cl-]",
   "[C-4]", "[C+4]", "[Fe-2]", "[Ne]", "[*]", "[*+]", "[*-15]", "[*+15]",
   "[13CH3][NH3+].[Cl-]", "c1cc[nH+]cc1", "C[N+](C)(C)C"]

/-- Must parse and fail `checkCharges`. -/
def inconsistent : List String :=
  ["[C+123]", "[C-123]", "[H+++]", "[C+++++++]", "[C+7]", "[C-5]", "[O-3]", "[H-2]", "[H+2]",
   "[Ne-]", "[*+16]", "[*-16]", "C[C+123]", "[Na+].[Cl-99]"]

def hasSubstring (s sub : String) : Bool := (s.splitOn sub).length > 1

public def main : IO UInt32 := do
  let mut failures : Array String := #[]
  for s in consistent do
    match parse s with
    | .error e => failures := failures.push s!"{s}: must parse, got {e}"
    | .ok M =>
      match M.checkCharges with
      | .ok () => pure ()
      | .error msg => failures := failures.push s!"{s}: must pass checkCharges, got: {msg}"
  for s in inconsistent do
    match parse s with
    | .error e => failures := failures.push s!"{s}: must parse, got {e}"
    | .ok M =>
      match M.checkCharges with
      | .ok () => failures := failures.push s!"{s}: must fail checkCharges"
      | .error msg => IO.println s!"  {s}: {msg}"
  -- The message names the atom index, element symbol and charge.
  match parse "C[C+123]" with
  | .error e => failures := failures.push s!"C[C+123]: must parse, got {e}"
  | .ok M =>
    match M.checkCharges with
    | .ok () => failures := failures.push "C[C+123]: must fail checkCharges"
    | .error msg =>
      unless msg.startsWith "atom 1 (C)" && hasSubstring msg "+123" do
        failures := failures.push s!"C[C+123]: message should name atom 1, C and +123: {msg}"
  -- `[Fe+++]` and `[Fe+3]` are the same atom.
  match parse "[Fe+++]", parse "[Fe+3]" with
  | .ok A, .ok B =>
    unless A.canonicalSmiles == B.canonicalSmiles do
      failures := failures.push
        s!"[Fe+++] and [Fe+3] differ: {A.canonicalSmiles} vs {B.canonicalSmiles}"
  | _, _ => failures := failures.push "[Fe+++] or [Fe+3] failed to parse"
  -- Relabeling and canonicalization preserve the verdict, as the theorems say.
  for s in consistent ++ inconsistent do
    if let .ok M := parse s then
      let v := decide M.chargesConsistent
      if decide M.canonicalize.chargesConsistent != v then
        failures := failures.push s!"{s}: canonicalization changed the charge verdict"
      if decide (M.relabel Fin.revPerm).chargesConsistent != v then
        failures := failures.push s!"{s}: relabeling changed the charge verdict"
  IO.println s!"{consistent.length} consistent, {inconsistent.length} inconsistent; \
    {failures.size} failures"
  for f in failures do
    IO.println s!"  {f}"
  return if failures.isEmpty then 0 else 1
