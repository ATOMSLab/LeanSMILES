/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Resonance
public import LeanSMILES.Tests.OracleRow
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Resonance test: the specification of `LeanSMILES.Aromaticity.Resonance` on the data

For every molecule, take a Kekulé structure and enumerate its Kekulé partners:
every way to trade single and double ring bonds that keeps each atom's number of
double bonds (up to `cap` of them). Then check:

1. `AromaticBondsKekuleInvariant`: every partner gets the same aromatic bonds.
2. `AromatizeMergesExactlyResonance`: for every pair of partners, they aromatize
   to one molecule exactly when they differ only on aromatic bonds.
3. `AromatizeRelabelKekule`: renumbering the Kekulé structure and then
   aromatizing gives the aromatized molecule renumbered.

`AromatizeRelabel` (property 3 on the input as written, lowercase included) is
reported for information; it is known to fail.

The report also counts, per molecule, the distinct canonical SMILES over the
partners before and after aromatization, and lists molecules whose partners
stay apart after aromatization: those are where the aromaticity model, not the
graph, decides what counts as one molecule.

    lake exe resonance-test

Kekulé structures come from RDKit's Kekulé oracle files and, for the EGFR set
and the hand-picked cases, from this library's kekulizer.
-/

open LeanSMILES LeanSMILES.Aromaticity LeanSMILES.Tests

namespace LeanSMILES.Tests.Resonance

variable {n : ℕ}

/-- The kekulizer alone: lowercase input to one Kekulé structure, the first step of
`Molecule.aromatize` without the perception that follows. -/
def kekuleForm (m : Molecule n) : Except String (Molecule n) := do
  let w := (Work.ofMolecule m).freezeHs.cleanUp.cacheValences
  let w ← w.kekulize w.relevantCycles
  let atoms := Vector.ofFn fun i : Fin n ↦
    { m.atom i with aromatic := false, charge := (w.atoms[i.val]!).charge }
  return { atoms, bonds := withKinds m w, nodup := map_edge_withKinds m w ▸ m.nodup }

/-- Whether bond `k` lies on a cycle: its endpoints are still joined without it. -/
def onCycle (m : Molecule n) (k : ℕ) : Bool := Id.run do
  let some b := m.bonds[k]? | return false
  let others := (m.bonds.zipIdx.filter (·.2 != k)).map fun (b', _) ↦ (b'.src.val, b'.dst.val)
  let mut seen := (Array.replicate n false).set! b.src.val true
  for _ in [0:n] do
    for (u, v) in others do
      if seen[u]! && !seen[v]! then seen := seen.set! v true
      if seen[v]! && !seen[u]! then seen := seen.set! u true
  return seen[b.dst.val]!

/-- Backtracking over the tradable bonds `flex`: each becomes double or single, and every atom
must end with `need` double bonds among them. `got` counts the doubles placed so far and `left`
the undecided tradable bonds at each atom. Returns the sets of doubled bonds, at most `cap`. -/
def search (ends : Array (ℕ × ℕ)) (need : Array ℕ) (cap : ℕ) :
    List ℕ → Array ℕ → Array ℕ → List ℕ → Array (List ℕ) → Array (List ℕ)
  | [], got, _, chosen, acc => if got == need then acc.push chosen else acc
  | k :: rest, got, left, chosen, acc =>
    if cap ≤ acc.size then acc else
    let (u, v) := ends[k]!
    let left' := (left.modify u (· - 1)).modify v (· - 1)
    let acc :=
      if got[u]! < need[u]! && got[v]! < need[v]! then
        search ends need cap rest ((got.modify u (· + 1)).modify v (· + 1)) left' (k :: chosen) acc
      else acc
    if need[u]! ≤ got[u]! + left'[u]! && need[v]! ≤ got[v]! + left'[v]! then
      search ends need cap rest got left' chosen acc
    else acc

/-- The Kekulé partners of `m` (including `m`), at most `cap`: every way to trade single and
double bonds on cycles that keeps each atom's number of double bonds. -/
def partners (m : Molecule n) (cap : ℕ) : List (Molecule n) :=
  let kinds := m.bonds.map (·.kind)
  let ends := (m.bonds.map fun b ↦ (b.src.val, b.dst.val)).toArray
  let flex := (List.range m.bonds.length).filter fun k ↦
    (kinds[k]? == some .single || kinds[k]? == some .double) && onCycle m k
  let isFlex := flex.foldl (fun a k ↦ a.set! k true) (Array.replicate m.bonds.length false)
  let need := flex.foldl (init := Array.replicate n 0) fun a k ↦
    if kinds[k]? == some .double then (a.modify ends[k]!.1 (· + 1)).modify ends[k]!.2 (· + 1)
    else a
  let left := flex.foldl (init := Array.replicate n 0) fun a k ↦
    (a.modify ends[k]!.1 (· + 1)).modify ends[k]!.2 (· + 1)
  let sols := search ends need cap flex (Array.replicate n 0) left [] #[]
  sols.toList.map fun dbl ↦
    let isDbl := dbl.foldl (fun a k ↦ a.set! k true) (Array.replicate m.bonds.length false)
    m.setKinds fun k kind ↦
      if isFlex[k]! then (if isDbl[k]! then .double else .single) else kind

/-- A few renumberings of `n` atoms: rotations, the reversal, and products of swaps. -/
def perms (n : ℕ) : List (Equiv.Perm (Fin n)) :=
  match n with
  | 0 => []
  | k + 1 =>
    let swaps (seed : ℕ) : Equiv.Perm (Fin (k + 1)) :=
      (List.range (2 * (k + 1))).foldl (init := Equiv.refl _) fun σ t ↦
        let a : Fin (k + 1) := ⟨(seed * 7919 + t * 104729) % (k + 1), Nat.mod_lt _ (by omega)⟩
        let b : Fin (k + 1) := ⟨(seed * 15485863 + t * t * 31 + 3) % (k + 1),
          Nat.mod_lt _ (by omega)⟩
        σ.trans (Equiv.swap a b)
    [finRotate _, Fin.revPerm, (finRotate _).trans (finRotate _), swaps 1, swaps 2, swaps 3]

/-- Tallies over one input set. -/
structure Tally where
  /-- Molecules read. -/
  molecules : ℕ := 0
  /-- Molecules with more than one Kekulé partner. -/
  withPartners : ℕ := 0
  /-- Molecules whose enumeration hit the cap. -/
  capped : ℕ := 0
  /-- Enumerated structures that fail `KekulePartner` (a bug in the enumeration). -/
  notPartners : ℕ := 0
  /-- Molecules where property 1 fails. -/
  fail1 : ℕ := 0
  /-- Pairs checked for property 2. -/
  pairs : ℕ := 0
  /-- Pairs where property 2 fails. -/
  fail2 : ℕ := 0
  /-- Molecules where property 3 fails as molecules. -/
  fail3 : ℕ := 0
  /-- Molecules where property 3 fails even for the canonical string. -/
  fail3canon : ℕ := 0
  /-- Molecules whose partners have more than one canonical SMILES before aromatization. -/
  splitBefore : ℕ := 0
  /-- Molecules whose partners have more than one canonical SMILES after aromatization. -/
  splitAfter : ℕ := 0
  /-- Examples to print. -/
  notes : Array String := #[]

/-- Record an example, keeping at most twelve of each kind. -/
def Tally.note (t : Tally) (s : String) : Tally :=
  if (t.notes.filter (·.startsWith (s.take 6).toString)).size < 12 then
    { t with notes := t.notes.push s } else t

/-- The aromatized molecule, if aromatization succeeds. -/
def arom (m : Molecule n) : Option (Molecule n) := m.aromatize.toOption

/-- Run the checks on one Kekulé structure `k`, labelled `label` in the report. -/
def checkKekule (t : Tally) (label : String) (k : Molecule n) (cap : ℕ) : Tally := Id.run do
  let mut t := { t with molecules := t.molecules + 1 }
  if !decide k.IsKekule then
    return t.note s!"skip   {label}: not a Kekulé structure"
  let ps := partners k cap
  if 1 < ps.length then t := { t with withPartners := t.withPartners + 1 }
  if cap ≤ ps.length then t := { t with capped := t.capped + 1 }
  let bad := ps.filter fun p ↦ !decide (k.KekulePartner p)
  if !bad.isEmpty then t := { t with notPartners := t.notPartners + bad.length }
  let as := ps.map fun p ↦ (p, arom p)
  -- property 1
  let ab := as.map fun (_, a) ↦ a.map Molecule.aromaticBonds
  if ab.any (· != ab.headD none) then
    t := { t with fail1 := t.fail1 + 1 }
    t := t.note s!"prop1  {label}"
  -- property 2, every ordered pair
  let mut f2 := 0
  for (p, ap) in as do
    if let some a := ap then
      for (q, aq) in as do
        t := { t with pairs := t.pairs + 1 }
        if (aq == some a) != p.differOnlyOn q a.aromaticBonds then f2 := f2 + 1
  if 0 < f2 then
    t := { t with fail2 := t.fail2 + f2 }
    t := t.note s!"prop2  {label}: {f2} pairs"
  -- property 3
  let a := arom k
  let c := k.aromaticCanonicalSmiles
  let molFail := (perms n).any fun σ ↦ arom (k.relabel σ) != a.map (·.relabel σ)
  let canFail := (perms n).any fun σ ↦ (k.relabel σ).aromaticCanonicalSmiles != c
  if molFail then t := { t with fail3 := t.fail3 + 1 }
  if canFail then
    t := { t with fail3canon := t.fail3canon + 1 }
    t := t.note s!"prop3  {label}"
  -- canonical SMILES over the partners, before and after aromatization
  let before := (ps.map Molecule.canonicalSmiles).eraseDups
  let after := (ps.map Molecule.aromaticCanonicalSmiles).eraseDups
  if 1 < before.length then t := { t with splitBefore := t.splitBefore + 1 }
  if 1 < after.length then
    t := { t with splitAfter := t.splitAfter + 1 }
    let shown := (after.take 3).map fun s ↦ s.getD "-"
    t := t.note s!"apart  {label}: {ps.length} partners, {after.length} after \
      aromatize: {", ".intercalate shown}"
  return t

/-- Print a tally; true when properties 1–3 held on every molecule. -/
def report (name : String) (t : Tally) : IO Bool := do
  IO.println s!"{name}: {t.molecules} Kekulé structures, {t.withPartners} with more than one \
    partner, {t.capped} capped"
  IO.println s!"  enumeration: structures that are not Kekulé partners {t.notPartners}  [must be 0]"
  IO.println s!"  1 aromatic bonds the same over the partners: fails on {t.fail1}  [spec]"
  IO.println s!"  2 same molecule ↔ differ only on aromatic bonds: fails on {t.fail2} of \
    {t.pairs} pairs  [spec]"
  IO.println s!"  3 aromatize commutes with renumbering: fails on {t.fail3} as molecules, \
    {t.fail3canon} as canonical SMILES  [spec]"
  IO.println s!"  partners with more than one canonical SMILES: before aromatize {t.splitBefore}, \
    after {t.splitAfter}  [info]"
  for s in t.notes do
    IO.println s!"    {s}"
  return t.notPartners == 0 && t.fail1 == 0 && t.fail2 == 0 && t.fail3canon == 0

/-- `AromatizeRelabel` on molecules as written: count those whose aromatic canonical SMILES
depends on the numbering. -/
def checkAsWritten (name : String) (smiles : List String) : IO Unit := do
  let mut total := 0
  let mut fails : Array String := #[]
  for s in smiles do
    if let .ok M := SMILES.parse s then
      total := total + 1
      let c := M.mol.aromaticCanonicalSmiles
      if (perms M.n).any fun σ ↦ (M.mol.relabel σ).aromaticCanonicalSmiles != c then
        fails := fails.push s
  IO.println s!"{name} as written: {total} molecules, aromatic canonical SMILES depends on the \
    numbering for {fails.size}  [info: AromatizeRelabel]"
  for s in fails.toList.take 8 do
    IO.println s!"    {s}"

/-- Hand-picked cases, written lowercase where aromatic. -/
def handPicked : List String :=
  ["Cc1ccccc1C", "c1ccc2ccccc2c1", "c1ccc2cc3ccccc3cc2c1", "c1ccc2c(c1)ccc1ccccc12",
   "c1cc2ccc3cccc4ccc(c1)c2c34", "Cc1ccccccc1C", "c1ccccccc1", "c1ccc2c(c1)-c1ccccc1-2",
   "c1ccc2cccc2cc1", "Cc1cccc2ncc12", "c1ccc2ncncc2c1", "c1ccc2[nH]ccc2c1",
   "c1ccccccccccccccccc1", "Cc1ccc2ccc3cccc4c3c2c1cc4", "O=c1cccccc1", "c1ccc2c(c1)C=Cc1ccccc1-2"]

/-- The `smiles` column (second) of a CSV file with a header. -/
def smilesColumn (path : String) : IO (List String) := do
  let lines ← IO.FS.lines path
  return (lines.toList.drop 1).filterMap fun l ↦ (l.splitOn ",")[1]?

/-- Kekulé structures from lowercase SMILES, by this library's kekulizer. -/
def viaKekulizer (smiles : List String) : List (String × Mol) :=
  smiles.filterMap fun s ↦
    match SMILES.parse s with
    | .ok M => (kekuleForm M.mol).toOption.map fun k ↦ (s, ⟨M.n, k⟩)
    | .error _ => none

/-- Kekulé structures from Kekulé SMILES, parsed as written. -/
def parsed (smiles : List String) : List (String × Mol) :=
  smiles.filterMap fun s ↦ (SMILES.parse s).toOption.map (s, ·)

end LeanSMILES.Tests.Resonance

open LeanSMILES.Tests.Resonance in
/-- Entry point of `lake exe resonance-test`. -/
public def main (_ : List String) : IO UInt32 := do
  let cap := 64
  let mut ok := true
  let kekuleFiles := ["datasets/delaney-kekule-oracle.csv",
    "datasets/aromaticity-cases-kekule-oracle.csv", "datasets/isotope-cases-kekule-oracle.csv",
    "datasets/hydrogen-cases-kekule-oracle.csv"]
  for p in kekuleFiles do
    let rows ← readRows p
    let t := (parsed (rows.map (·.smiles))).foldl (init := {})
      fun t (s, M) ↦ checkKekule t s M.mol cap
    if !(← report p t) then ok := false
  let egfr ← smilesColumn "datasets/egfr-classification.csv"
  let sets := [("datasets/egfr-classification.csv (kekulized)", viaKekulizer egfr),
    ("hand-picked (kekulized)", viaKekulizer handPicked)]
  for (name, ms) in sets do
    let t := ms.foldl (init := {}) fun t (s, M) ↦ checkKekule t s M.mol cap
    if !(← report name t) then ok := false
  for p in ["datasets/delaney-oracle.csv", "datasets/aromaticity-cases-oracle.csv"] do
    checkAsWritten p ((← readRows p).map (·.smiles))
  checkAsWritten "datasets/egfr-classification.csv" egfr
  checkAsWritten "hand-picked" handPicked
  return if ok then 0 else 1
