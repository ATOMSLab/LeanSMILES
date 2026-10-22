/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
import LeanSMILES.SMILES.Parse

/-!
# LeanSMILES.Tests.Validity

Does the parser accept exactly the SMILES that RDKit accepts?

`datasets/fuzz-validity.tsv` (from `tools/rdkit_fuzz.py` on the
`canonical-smiles` branch) holds 10 000 randomly broken SMILES, each tagged
`1` or `0` for whether RDKit's `MolFromSmiles` accepted it.

RDKit rejects a string for two kinds of reason — syntax, and chemistry
(valence) found by sanitization.  This parser checks syntax only, so the two
directions of disagreement mean different things:

* **RDKit accepts, Lean rejects** — a parser bug.  Must be zero, except for
  the rejections `ParseError.isGrammarDeviation` names: the OpenSMILES grammar
  overruling RDKit by decision (today, a ring-closure label after a branch,
  `C(C)1CC1`).  Those are counted and listed separately.
* **Lean accepts, RDKit rejects** — expected: RDKit's valence model rejected
  a syntactically valid string.  Reported, with examples, for information.

```
lake exe validity-test [datasets/fuzz-validity.tsv]
```
-/

open LeanSMILES LeanSMILES.SMILES

def main (args : List String) : IO UInt32 := do
  let path := args.headD "datasets/fuzz-validity.tsv"
  let lines ← IO.FS.lines path
  let mut total := 0
  let mut agree := 0
  let mut rdkitOnly : Array (String × ParseError) := #[]
  let mut deviations : Array (String × ParseError) := #[]
  let mut leanOnly : Array String := #[]
  for line in lines do
    match line.splitOn "\t" with
    | [verdict, s] =>
      total := total + 1
      let rdkitAccepts := verdict == "1"
      match parse s with
      | .ok _ => if rdkitAccepts then agree := agree + 1 else leanOnly := leanOnly.push s
      | .error e =>
        if !rdkitAccepts then agree := agree + 1
        else if e.isGrammarDeviation then deviations := deviations.push (s, e)
        else rdkitOnly := rdkitOnly.push (s, e)
    | _ => pure ()
  IO.println s!"{total} strings; {agree} agree with RDKit"
  IO.println s!"RDKit accepts, Lean rejects (parser bugs): {rdkitOnly.size}"
  for (s, e) in rdkitOnly.toList.take 20 do
    IO.println s!"  {s}\n    {e}"
  IO.println
    s!"RDKit accepts, Lean rejects by the OpenSMILES grammar (deliberate): {deviations.size}"
  for (s, e) in deviations.toList.take 20 do
    IO.println s!"  {s}\n    {e}"
  IO.println s!"Lean accepts, RDKit rejects (RDKit valence/semantic checks): {leanOnly.size}"
  for s in leanOnly.toList.take 10 do
    IO.println s!"  {s}"
  return if rdkitOnly.isEmpty then 0 else 1
