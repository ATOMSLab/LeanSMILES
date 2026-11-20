/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.SMILES.KekuleClass
public import LeanSMILES.Aromaticity.Perceive
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Kekulé-class benchmark: what `Molecule.kekuleCanonicalSmiles` costs

`kekuleCanonicalSmiles` writes the movable bonds of a molecule (double in some Kekulé partner,
single in another) aromatic and canonicalizes the result once. The spec finds the movable bonds by
trying all `2 ^ numBonds` placements of double bonds (`Molecule.movable`), which only runs on
small molecules. This file finds them fast: for each bond that can trade (single or double, on a
cycle), one backtracking search for a partner with that bond flipped (`movableFast`).

For each molecule it reports:

* the cost of the fast version: the movable bonds, then one canonical SMILES;
* the cost of the old design, the least canonical SMILES over all Kekulé partners (measured up to
  1000 partners, estimated beyond);
* checks: the fast movable bonds agree with the spec (up to `specLimit` bonds) and with full
  enumeration (whenever the partners are not capped); every partner gets the same string (up to
  `partnerLimit` of them); renumbering the atoms does not change it.

Worst cases: acenes, coronene, hexabenzocoronene, kekulene, circumcoronene, C60 and C70 (Kekulé
SMILES from PubChem), then every molecule of the Delaney and EGFR sets.

    lake exe kekule-bench
-/

@[expose] public section

open LeanSMILES LeanSMILES.Aromaticity

namespace LeanSMILES.Tests.KekuleBench

variable {n : ℕ}

/-- The kekulizer alone, for the lowercase EGFR SMILES. -/
def kekuleForm (m : Molecule n) : Except String (Molecule n) := do
  let w := Work.prepare m
  let w ← w.kekulize w.relevantCycles
  let atoms := Vector.ofFn fun i : Fin n ↦
    { m.atom i with aromatic := false, charge := (w.atoms[i.val]!).charge }
  return { atoms, bonds := withKinds m w, nodup := map_edge_withKinds m w ▸ m.nodup,
           stereo := m.stereo }

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

/-- Backtracking over the tradable bonds: each becomes double or single, and every atom must end
with `need` double bonds among them. At most `cap` solutions. -/
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

/-- The tradable bonds: single or double, on a cycle. -/
def flex (m : Molecule n) : List ℕ :=
  (List.range m.bonds.length).filter fun k ↦
    (m.bonds[k]?.map (·.kind) == some .single || m.bonds[k]?.map (·.kind) == some .double) &&
      onCycle m k

/-- The Kekulé partners of `m`, at most `cap`, found by search. -/
def partners (m : Molecule n) (fl : List ℕ) (cap : ℕ) : List (Molecule n) :=
  let kinds := m.bonds.map (·.kind)
  let ends := (m.bonds.map fun b ↦ (b.src.val, b.dst.val)).toArray
  let isFlex := fl.foldl (fun a k ↦ a.set! k true) (Array.replicate m.bonds.length false)
  let need := fl.foldl (init := Array.replicate n 0) fun a k ↦
    if kinds[k]? == some .double then (a.modify ends[k]!.1 (· + 1)).modify ends[k]!.2 (· + 1)
    else a
  let left := fl.foldl (init := Array.replicate n 0) fun a k ↦
    (a.modify ends[k]!.1 (· + 1)).modify ends[k]!.2 (· + 1)
  let sols := search ends need cap fl (Array.replicate n 0) left [] #[]
  sols.toList.map fun dbl ↦
    let isDbl := dbl.foldl (fun a k ↦ a.set! k true) (Array.replicate m.bonds.length false)
    m.setKinds fun k kind ↦
      if isFlex[k]! then (if isDbl[k]! then .double else .single) else kind

/-- The spec's movable bonds are computed only up to this many bonds. -/
def specLimit : ℕ := 14

/-- At most this many partners are enumerated. -/
def cap : ℕ := 200000

/-- Partner invariance is checked on at most this many partners. -/
def partnerLimit : ℕ := 20

/-- Run `f` and time it in milliseconds; `force` makes sure the value is computed in between. -/
@[noinline] def timed {α : Type} (f : Unit → α) (force : α → ℕ) : IO (α × Float) := do
  let t₀ ← IO.monoNanosNow
  let a := f ()
  if force a == 987654321 then IO.println ""
  let t₁ ← IO.monoNanosNow
  return (a, (t₁ - t₀).toFloat / 1e6)

/-- `x` with one decimal. -/
def dec1 (x : Float) : String :=
  let t := (x * 10).round.toUInt64.toNat
  s!"{t / 10}.{t % 10}"

/-- Milliseconds, readably. -/
def fmt (ms : Float) : String :=
  if ms < 1000 then s!"{dec1 ms} ms"
  else if ms < 120000 then s!"{dec1 (ms / 1000)} s"
  else if ms < 7.2e6 then s!"{dec1 (ms / 60000)} min"
  else s!"{dec1 (ms / 3.6e6)} h"

/-- What the search needs: bond endpoints, each atom's double bonds among the tradable bonds and
its number of tradable bonds, the tradable bonds, and which bonds are double. -/
structure Setup where
  ends : Array (ℕ × ℕ)
  need : Array ℕ
  left : Array ℕ
  fl : List ℕ
  isDouble : Array Bool

/-- The search's input for `m`. -/
def setup (m : Molecule n) : Setup :=
  let fl := flex m
  let kinds := m.bonds.map (·.kind)
  let ends := (m.bonds.map fun b ↦ (b.src.val, b.dst.val)).toArray
  let need := fl.foldl (init := Array.replicate n 0) fun a k ↦
    if kinds[k]? == some .double then (a.modify ends[k]!.1 (· + 1)).modify ends[k]!.2 (· + 1)
    else a
  let left := fl.foldl (init := Array.replicate n 0) fun a k ↦
    (a.modify ends[k]!.1 (· + 1)).modify ends[k]!.2 (· + 1)
  { ends, need, left, fl, isDouble := (kinds.map (· == .double)).toArray }

/-- Whether some placement of double bonds on `fl` meets `need`. -/
def solvable (st : Setup) (need left : Array ℕ) (fl : List ℕ) : Bool :=
  !(search st.ends need 1 fl (Array.replicate need.size 0) left [] #[]).isEmpty

/-- The movable bonds, by position: for each tradable bond, one search for a Kekulé partner with
that bond flipped. -/
def movableFast (m : Molecule n) : Array Bool :=
  let st := setup m
  st.fl.foldl (init := Array.replicate m.bonds.length false) fun mask k ↦
    let (u, v) := st.ends[k]!
    let left' := (st.left.modify u (· - 1)).modify v (· - 1)
    let fl' := st.fl.erase k
    let flips :=
      if st.isDouble[k]! then solvable st st.need left' fl'
      else 0 < st.need[u]! && 0 < st.need[v]! &&
        solvable st ((st.need.modify u (· - 1)).modify v (· - 1)) left' fl'
    if flips then mask.set! k true else mask

/-- A mask as a function. -/
def lookup (mask : Array Bool) (k : ℕ) : Bool := mask[k]?.getD false

/-- The movable bonds as the spec defines them, by position. -/
def movableSpec (m : Molecule n) : Array Bool := ((List.range m.numBonds).map m.movable).toArray

/-- The movable bonds read off a list of partners. -/
def movableEnum (m : Molecule n) (ps : List (Molecule n)) : Array Bool :=
  ((List.range m.numBonds).map fun k ↦
    ps.any (·.kindAt k == some .double) && ps.any (·.kindAt k == some .single)).toArray

/-- The fast Kekulé canonical SMILES. -/
def fastCanonical (m : Molecule n) : String :=
  (m.delocalizeWith (lookup (movableFast m))).canonicalSmiles

/-- One measured molecule. -/
structure Row where
  bonds : ℕ
  partners : ℕ
  capped : Bool
  movable : ℕ
  maskMs : Float
  canonMs : Float
  oldMs : Float
  oldEstimated : Bool
  specAgrees : Option Bool
  enumAgrees : Option Bool
  partnersAgree : Bool
  relabelAgrees : Bool
  string : String

/-- Measure one Kekulé structure. -/
def measure (m : Molecule n) (partnersForOld : ℕ) : IO Row := do
  let (mask, maskMs) ← timed (fun _ ↦ movableFast m) fun a ↦ (a.toList.filter id).length
  let (s, canonMs) ← timed (fun _ ↦ (m.delocalizeWith (lookup mask)).canonicalSmiles) String.length
  let ps := partners m (flex m) cap
  let capped := cap ≤ ps.length
  let (oldMs, oldEstimated) ←
    if ps.length ≤ partnersForOld then do
      let (_, t) ← timed (fun _ ↦ (ps.map Molecule.canonicalSmiles).min?) fun o ↦ (o.getD "").length
      pure (t, false)
    else do
      let (_, t) ← timed (fun _ ↦ m.canonicalSmiles) String.length
      pure (t * ps.length.toFloat, true)
  let specAgrees :=
    if m.numBonds ≤ specLimit then some (movableSpec m == mask) else none
  let enumAgrees := if capped then none else some (movableEnum m ps == mask)
  let partnersAgree := (ps.take partnerLimit).all fun p ↦ fastCanonical p == s
  let relabelAgrees := [finRotate n, Fin.revPerm, (finRotate n).trans Fin.revPerm].all fun σ ↦
    fastCanonical (m.relabel σ) == s
  return { bonds := m.numBonds, partners := ps.length, capped,
           movable := (mask.toList.filter id).length, maskMs, canonMs, oldMs, oldEstimated,
           specAgrees, enumAgrees, partnersAgree, relabelAgrees, string := s }

/-- The checks of a row, as a word. -/
def Row.checks (r : Row) : String :=
  let bad := [("spec", r.specAgrees == some false), ("enumeration", r.enumAgrees == some false),
    ("partners", !r.partnersAgree), ("renumbering", !r.relabelAgrees)].filter (·.2)
  if bad.isEmpty then "ok" else "FAILS " ++ ", ".intercalate (bad.map (·.1))

set_option linter.style.longLine false in
/-- The worst-case molecules, as Kekulé SMILES. -/
def worstCases : List (String × String) := [
  ("benzene", "C1=CC=CC=C1"),
  ("naphthalene", "C1=CC=C2C=CC=CC2=C1"),
  ("biphenylene", "C1=CC=C2C(=C1)-C1=CC=CC=C1-2"),
  ("anthracene", "C1=CC=C2C=C3C=CC=CC3=CC2=C1"),
  ("tetracene", "C1=CC=C2C=C3C=C4C=CC=CC4=CC3=CC2=C1"),
  ("pentacene", "C1=CC=C2C=C3C=C4C=C5C=CC=CC5=CC4=CC3=CC2=C1"),
  ("hexacene", "C1=CC=C2C=C3C=C4C=C5C=C6C=CC=CC6=CC5=CC4=CC3=CC2=C1"),
  ("coronene", "C1=CC2=C3C4=C1C=CC5=C4C6=C(C=C5)C=CC7=C6C3=C(C=C2)C=C7"),
  ("hexabenzocoronene", "C1=CC2=C3C=CC=C4C3=C5C6=C2C(=C1)C7=C8C6=C9C1=C(C8=CC=C7)C=CC=C1C1=CC=CC2=C1C9=C5C1=C4C=CC=C21"),
  ("kekulene", "C1=CC2=CC3=C4C=C2C5=CC6=C(C=CC7=CC8=C(C=C76)C9=CC2=C(C=CC6=C2C=C2C(=C6)C=CC6=C2C=C4C(=C6)C=C3)C=C9C=C8)C=C51"),
  ("circumcoronene", "C1=CC2=CC3=C4C5=C6C7=C(C=CC8=CC9=C%10C%11=C(C=C9)C=C9C=CC%12=C%13C9=C%11C9=C%11C%13=C%13C(=C%12)C=CC%12=C%13C%13=C%11C(=C4C2=C%13C1=C%12)C6=C9C%10=C87)C=C5C=C3"),
  ("C60", "C12=C3C4=C5C6=C1C7=C8C9=C1C%10=C%11C(=C29)C3=C2C3=C4C4=C5C5=C9C6=C7C6=C7C8=C1C1=C8C%10=C%10C%11=C2C2=C3C3=C4C4=C5C5=C%11C%12=C(C6=C95)C7=C1C1=C%12C5=C%11C4=C3C3=C5C(=C81)C%10=C23"),
  ("C70", "C12=C3C4=C5C6=C7C8=C9C%10=C%11C%12=C%13C%10=C%10C8=C5C1=C%10C1=C%13C5=C8C1=C2C1=C3C2=C3C%10=C%13C%14=C3C1=C8C1=C3C5=C%12C5=C8C%11=C%11C9=C7C7=C9C6=C4C2=C2C%10=C4C(=C29)C2=C6C(=C8C8=C9C6=C4C%13=C9C(=C%141)C3=C85)C%11=C27")]

/-- `s` padded to width `w`. -/
def col (w : ℕ) (s : String) : String := s.pushn ' ' (w - s.length)

/-- Print and flush. -/
def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-- One line per worst case. -/
def worstCaseReport : IO Unit := do
  say <| col 19 "molecule" ++ col 7 "bonds" ++ col 12 "structures" ++ col 9 "movable" ++
    col 22 "fast: mask + canon" ++ col 24 "old: min over class" ++ "checks"
  for (label, smi) in worstCases do
    match SMILES.parse smi with
    | .error _ => say s!"{label}: parse error"
    | .ok M =>
      let r ← measure M.mol 1000
      say <| col 19 label ++ col 7 (toString r.bonds) ++
        col 12 (toString r.partners ++ if r.capped then "+" else "") ++
        col 9 (toString r.movable) ++
        col 22 (fmt r.maskMs ++ " + " ++ fmt r.canonMs) ++
        col 24 ((if r.oldEstimated then "~" else "") ++ fmt r.oldMs) ++ r.checks
      say s!"    {r.string}"

/-- The SMILES column of a CSV. -/
def smilesColumn (path : String) : IO (List String) := do
  let lines ← IO.FS.lines path
  return (lines.toList.drop 1).filterMap fun l ↦ (l.splitOn ",")[1]?

/-- Totals over a dataset. -/
def datasetReport (name : String) (mols : List Mol) : IO Unit := do
  let mut maxBonds := 0
  let mut maxPartners := 0
  let mut fast := 0.0
  let mut slowest := 0.0
  let mut old := 0.0
  let mut specRuns := 0
  let mut failures : List String := []
  for M in mols do
    let r ← measure M.mol 1000
    maxBonds := max maxBonds r.bonds
    maxPartners := max maxPartners r.partners
    fast := fast + r.maskMs + r.canonMs
    slowest := max slowest (r.maskMs + r.canonMs)
    old := old + r.oldMs
    if r.specAgrees.isSome then specRuns := specRuns + 1
    if r.checks != "ok" then failures := failures ++ [s!"{r.string}: {r.checks}"]
  say s!"{name}: {mols.length} molecules, at most {maxBonds} bonds and {maxPartners} Kekulé \
    structures"
  say s!"  fast: {fmt fast} in all, slowest {fmt slowest}; old: {fmt old} in all"
  say s!"  checks: spec on {specRuns}, enumeration, partners and renumbering on all: \
    {failures.length} failures"
  for f in failures.take 10 do say s!"    {f}"

end LeanSMILES.Tests.KekuleBench

open LeanSMILES.Tests.KekuleBench in
/-- Entry point of `lake exe kekule-bench`. -/
def main : IO Unit := do
  worstCaseReport
  let delaney ← smilesColumn "datasets/delaney-kekule-oracle.csv"
  datasetReport "datasets/delaney-kekule-oracle.csv"
    (delaney.filterMap fun s ↦ (SMILES.parse s).toOption)
  let egfr ← smilesColumn "datasets/egfr-classification.csv"
  datasetReport "datasets/egfr-classification.csv (kekulized)"
    (egfr.filterMap fun s ↦ match SMILES.parse s with
      | .ok M => (kekuleForm M.mol).toOption.map fun k ↦ ⟨M.n, k⟩
      | .error _ => none)
