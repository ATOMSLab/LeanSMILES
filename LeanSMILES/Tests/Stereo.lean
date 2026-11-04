/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.SMILES.Canon
public import LeanSMILES.Depict.Layout
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# LeanSMILES.Tests.Stereo

Stereochemistry against RDKit and InChI, on the two files
`tools/rdkit_stereo.py` writes (`datasets/stereo-canon.tsv`,
`datasets/stereo-parity.tsv`).

**Canonical SMILES draws the stereo line where RDKit and InChI do, which must
hold.**  Rows come in families: one constitution, several stereoisomers, each
written several ways.  For every pair of rows in a family, RDKit's canonical
isomeric SMILES and the standard InChI say whether the two are the same
molecule — the file stores them compactly, as RDKit's string numbered within
the family and the stereo layers of the InChI, the rest of which is the
family's constitution — and when they agree, our canonical SMILES must agree
with them:

* *same molecule, same string* — the canonical SMILES does not depend on how
  the molecule was written (this is where a mark read against the wrong
  neighbor order shows up);
* *different stereoisomers, different strings* — split by what differs, read
  off the InChI layers: tetrahedral centres only (`/t /m /s`), double bonds
  only (`/b`), or both.

Pairs on which RDKit and InChI disagree are counted, not judged.  RDKit's
string itself is never compared with ours.  The first string of every
stereoisomer must also survive the checks `oracle-test` makes on the Delaney
set: the canonical SMILES reparses to itself, and relabeling the atoms
(`finRotate`, `Fin.revPerm`) does not change it.  Progress, and any row that
takes over two seconds, is printed to stderr.

**The parser reads each mark the way RDKit does, which must hold.**  For every
tetrahedral centre RDKit keeps, the mark the centre would carry with its
neighbors in ascending atom order (an implicit hydrogen or lone pair last); for
every stereo double bond RDKit keeps outside a ring, cis or trans for each pair
of substituents — including a substituent without a `/` `\\` of its own, whose
side follows from its partner's.  The answers come from a 3D embedding, so the two sides share
no neighbor-order convention.  Marks the parser keeps on atoms RDKit does not
consider stereocentres are reported.

```
lake exe stereo-test [datasets/stereo-canon.tsv] [datasets/stereo-parity.tsv]
```
-/

open LeanSMILES LeanSMILES.SMILES LeanSMILES.Depict

namespace LeanSMILES.Tests.Stereo

/-- The rows of a tab-separated file, header dropped. -/
def readTsv (path : String) : IO (List (List String)) := do
  let lines ← IO.FS.lines path
  return (lines.toList.drop 1).filterMap fun l ↦
    if l.trimAscii.isEmpty then none else some (l.splitOn "\t")

/-- One row of `stereo-canon.tsv`, with our canonical SMILES (`none` when the
string does not parse). -/
structure CanonRow where
  /-- The `family` column: one constitution, `stereo:k` or `hard:name`. -/
  family : String
  /-- The `variant` column: one stereoisomer (`orig`, `mirror`, `iso1`, `hand3`, …). -/
  variant : String
  /-- The `smiles` column: one writing of the variant. -/
  smiles : String
  /-- The `rdkit_id` column: RDKit's canonical isomeric SMILES of the string, numbered within
  the family; equal ids, equal strings. -/
  rdkitId : String
  /-- The `inchi_stereo` column: the stereo layers of the string's standard InChI (`-` for none,
  empty when there is no InChI). -/
  inchiStereo : String
  /-- Our canonical SMILES of the string; `none` when it does not parse. -/
  ours : Option String

/-- The InChI layers that carry stereo: tetrahedral (`/t`, `/m`, `/s`) and
double bond (`/b`). -/
def inchiLayers (inchi : String) (tags : List Char) : List String :=
  (inchi.splitOn "/").filter fun l ↦ l.front ∈ tags

/-- What differs between two stereoisomers, by their InChI layers. -/
def stereoDifference (a b : String) : String :=
  let t := inchiLayers a ['t', 'm', 's'] != inchiLayers b ['t', 'm', 's']
  let d := inchiLayers a ['b'] != inchiLayers b ['b']
  if t && d then "both" else if d then "double bonds" else "tetrahedral"

/-- Counts of one category of pair: checked, passed, a few failures, and
every family with a failure. -/
structure Tally where
  /-- Pairs checked. -/
  total : ℕ := 0
  /-- Pairs that passed. -/
  ok : ℕ := 0
  /-- Descriptions of the first eight failures. -/
  examples : Array String := #[]
  /-- Every family with a failing pair, each once. -/
  families : Array String := #[]

/-- Count one pair, keeping its description among the first eight failures and its family
among the failing ones. -/
def Tally.add (t : Tally) (pass : Bool) (describe : Unit → String) (family : String := "") :
    Tally :=
  { total := t.total + 1, ok := t.ok + (if pass then 1 else 0)
    examples := if pass || 8 ≤ t.examples.size then t.examples else t.examples.push (describe ())
    families := if pass || family.isEmpty || t.families.contains family then t.families
      else t.families.push family }

/-- The summary line: label, passed over checked, and whether all must pass. -/
def Tally.line (t : Tally) (label tag : String) : String := s!"{label}: {t.ok}/{t.total}  [{tag}]"

/-- Whether every checked pair passed. -/
def Tally.passed (t : Tally) : Bool := t.ok == t.total

/-- Insert into an association list of tallies. -/
def bump (ts : List (String × Tally)) (k : String) (pass : Bool) (ex : Unit → String)
    (family : String) : List (String × Tally) :=
  match ts.find? (·.1 == k) with
  | some _ => ts.map fun (k', t) ↦ if k' == k then (k', t.add pass ex family) else (k', t)
  | none => ts ++ [(k, ({} : Tally).add pass ex family)]

/-- Our canonical SMILES of a string, if it parses. -/
def canonOf (s : String) : Option String :=
  match parse s with
  | .ok M => some M.canonicalSmiles
  | .error _ => none

/-- The canonical-SMILES checks; `true` when every judged pair and row passes. -/
def canonTest (path : String) : IO Bool := do
  let raw ← readTsv path
  -- per row: our canonical SMILES, then round trip and relabeling; progress
  -- and the slowest rows go to stderr, since one large molecule can take a while
  let mut rows : Array CanonRow := #[]
  let mut parsed : Tally := {}
  let mut roundTrip : Tally := {}
  let mut relabel : Tally := {}
  let mut slow : Array (ℕ × String) := #[]
  let start ← IO.monoMsNow
  for fields in raw do
    let [f, v, s, k, i] := fields | continue
    let t ← IO.monoMsNow
    match parse s with
    | .error _ =>
      rows := rows.push ⟨f, v, s, k, i, none⟩
      parsed := parsed.add false fun _ ↦ s!"{f}: {s} does not parse"
    | .ok M =>
      let c := M.canonicalSmiles
      -- round trip and relabeling once per stereoisomer (its first string):
      -- the rewrites are what the pair checks are for
      let first := rows.all fun r ↦ r.family != f || r.variant != v
      rows := rows.push ⟨f, v, s, k, i, some c⟩
      parsed := parsed.add true fun _ ↦ ""
      if first then
        roundTrip := roundTrip.add (canonOf c == some c)
          fun _ ↦ s!"{f}: {s} → {c} → {canonOf c}"
        let c₁ := (M.relabel (finRotate M.n)).canonicalSmiles
        let c₂ := (M.relabel Fin.revPerm).canonicalSmiles
        relabel := relabel.add (c₁ == c && c₂ == c)
          fun _ ↦ s!"{f}: {s}: {c} / {c₁} / {c₂}"
    let dt := (← IO.monoMsNow) - t
    if 2000 ≤ dt then
      slow := slow.push (dt, s!"{f} {v}: {s}")
      IO.eprintln s!"  slow: {dt} ms for {f} {v} ({s.length} chars)"
    if rows.size % 500 == 0 then
      IO.eprintln s!"  {rows.size}/{raw.length} rows, {((← IO.monoMsNow) - start) / 1000} s"
  -- per pair within a family
  let families := rows.toList.splitBy (·.family == ·.family)
  let mut same : Tally := {}
  let mut different : List (String × Tally) := []
  let mut disputed : Tally := {}
  for fam in families do
    let fam := fam.toArray
    for hi : i in [0:fam.size] do
      for hj : j in [i + 1:fam.size] do
        let a := fam[i]
        let b := fam[j]
        let (some ca, some cb) := (a.ours, b.ours) | continue
        let rdSame := a.rdkitId == b.rdkitId
        let inSame :=
          if a.inchiStereo.isEmpty || b.inchiStereo.isEmpty then rdSame
          else a.inchiStereo == b.inchiStereo
        if rdSame != inSame then
          disputed := disputed.add false
            fun _ ↦ s!"{a.family}: {a.smiles} vs {b.smiles} \
              (RDKit {if rdSame then "same" else "different"})"
          continue
        let ex := fun (_ : Unit) ↦
          s!"{a.family} {a.variant}/{b.variant}: {a.smiles} → {ca}  vs  {b.smiles} → {cb}"
        if rdSame then same := same.add (ca == cb) ex a.family
        else
          let kind := stereoDifference a.inchiStereo b.inchiStereo
          different := bump different kind (ca != cb) ex a.family
  IO.println s!"stereo-canon: {rows.size} rows in {families.length} families"
  IO.println (parsed.line "parses" "must be all")
  IO.println (roundTrip.line "canonical SMILES survives reparse" "must be all")
  IO.println (relabel.line "canonical SMILES invariant under relabeling" "must be all")
  IO.println (same.line "same stereoisomer → same canonical SMILES (pairs)" "must be all")
  for (k, t) in different do
    IO.println
      (t.line s!"different stereoisomers ({k}) → different canonical SMILES (pairs)" "must be all")
  IO.println s!"pairs on which RDKit and InChI disagree, not judged: {disputed.total}"
  for t in [parsed, roundTrip, relabel, same] ++ different.map (·.2) ++ [disputed] do
    for e in t.examples do IO.println s!"  {e}"
  let labelled : List (String × Tally) :=
    ("same", same) :: different.map fun (p : String × Tally) ↦ (s!"different ({p.1})", p.2)
  for (label, t) in labelled do
    unless t.families.isEmpty do
      IO.println s!"families with a failing pair, {label}: {" ".intercalate t.families.toList}"
  return parsed.passed && roundTrip.passed && relabel.passed && same.passed
    && different.all (·.2.passed)

/-- Our mark at atom `i` in the convention of `stereo-parity.tsv`: `true` for
`@` with the neighbors in ascending atom order, an implicit hydrogen or lone
pair last — which is the listing `Graph.tetra` is relative to.  `none` when
the atom has no configuration. -/
def sortedMark (g : Graph) (i : ℕ) : Option Bool := g.tetraMark i

/-- The parser-parity checks; `true` when every centre and alkene agrees. -/
def parityTest (path : String) : IO Bool := do
  let raw ← readTsv path
  let mut parsed : Tally := {}
  let mut centers : Tally := {}
  let mut alkenes : Tally := {}
  let mut unread : Tally := {}
  let mut extra : Tally := {}
  for row in raw do
    let s := row.headD ""
    let wantCentres := (row.getD 1 "").splitOn " " |>.filter (· ≠ "") |>.filterMap fun e ↦
      match e.splitOn ":" with
      | [k, m] => k.toNat?.map (·, m == "@")
      | _ => none
    let wantAlkenes := (row.getD 2 "").splitOn " " |>.filter (· ≠ "") |>.filterMap fun e ↦
      match e.splitOn ":" with
      | [p, c] => match p.splitOn "-" with
        | [a, b] => do return (← a.toNat?, ← b.toNat?, c == "c")
        | _ => none
      | _ => none
    match parse s with
    | .error e => parsed := parsed.add false fun _ ↦ s!"{s}: {e}"
    | .ok M =>
      parsed := parsed.add true fun _ ↦ ""
      let g := Graph.ofMol M
      for (k, want) in wantCentres do
        let got := sortedMark g k
        centers := centers.add (got == some want)
          fun _ ↦ s!"{s}: atom {k} is {if want then "@" else "@@"} (sorted), \
            parser reads {got.map fun b ↦ if b then "@" else "@@"}"
      for k in [0:g.numAtoms] do
        if (g.tetraMark k).isSome && !(wantCentres.any (·.1 == k)) then
          extra := extra.add false fun _ ↦ s!"{s}: atom {k}"
      let (cis, all) := g.cisPairs
      for (a, c, wantCis) in wantAlkenes do
        let specified := all.contains (a, c) || all.contains (c, a)
        let gotCis := cis.contains (a, c) || cis.contains (c, a)
        unread := unread.add specified
          fun _ ↦ s!"{s}: {a},{c} {if wantCis then "cis" else "trans"}, parser reads nothing"
        if specified then
          alkenes := alkenes.add (gotCis == wantCis)
            fun _ ↦ s!"{s}: {a},{c} {if wantCis then "cis" else "trans"}, parser reads \
              {if gotCis then "cis" else "trans"}"
  IO.println s!"stereo-parity: {raw.length} strings"
  IO.println (parsed.line "parses" "must be all")
  IO.println (centers.line "tetrahedral centres read as RDKit reads them" "must be all")
  IO.println (alkenes.line
    "double-bond substituent pairs the parser reads, read as RDKit reads them"
    "must be all")
  IO.println (unread.line "double-bond substituent pairs the parser reads at all" "must be all")
  IO.println s!"marks on atoms RDKit does not keep as stereocentres: {extra.total}"
  for t in [parsed, centers, alkenes, unread, extra] do
    for e in t.examples do IO.println s!"  {e}"
  return parsed.passed && centers.passed && alkenes.passed && unread.passed

end LeanSMILES.Tests.Stereo

open LeanSMILES.Tests.Stereo in
public def main (args : List String) : IO UInt32 := do
  let canonOk ← canonTest (args.headD "datasets/stereo-canon.tsv")
  IO.println ""
  let parityOk ← parityTest ((args.drop 1).headD "datasets/stereo-parity.tsv")
  return if canonOk && parityOk then 0 else 1
