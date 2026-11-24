/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.Rings

/-!
# LeanSMILES.Aromaticity.Kekulize

Kekulization

Turns lowercase-aromatic input into an explicit alternating single/double
structure, as RDKit does before perceiving aromaticity (`Kekulize.cpp`,
`KekulizeFragment` with `canonical = false`). Ported from
`tools/rdkit_reference/aromaticity_ref.py` (`kekulize`).

Works one **fused ring system** at a time (rings sharing at least one bond):

1. **Which atoms need a double bond** (`markDbondCands`, `Kekulize.cpp:63-214`).
   Benzene `c` and pyridine `n` need one; pyrrole `[nH]`, furan `o` and `c(=O)`
   do not. All aromatic bonds of the system become single.
2. **Place the double bonds** with RDKit's own walk (`kekulizeWorker`,
   `Kekulize.cpp:217-436`): visit atoms through a queue, give each atom that
   needs one a double bond to its lowest-numbered neighbour that also needs one,
   and backtrack (at most 100 times) to the last atom that had other options.
   Following RDKit's walk exactly matters when a ring stays non-aromatic, since
   then the double-bond positions are visible in the result (`Cc1cccc2ncc12`).
3. **Clear aromatic flags** (`markAtomsBonds`, `Kekulize.cpp:748-777`).

## Main definitions

* `Aromaticity.Work.needsDoubleBond`: whether an aromatic atom needs a double bond.
* `Aromaticity.Work.KekState`: the state of `kekulizeWorker`'s walk.
* `Aromaticity.Work.kekulizeWorker`: RDKit's `kekulizeWorker` for one fused system.
* `Aromaticity.Work.kekulizeSystem`: one fused ring system of `Kekulize`.
* `Aromaticity.Work.kekulize`: RDKit's `Kekulize` over the fused ring systems.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity
namespace Work

/-- Does aromatic atom `i` need a double bond? `ev0` is its explicit valence before
kekulization; `wasAromatic k` says whether bond `k` was written aromatic (RDKit
keeps that flag during the whole kekulization). Per-atom part of `markDbondCands`. -/
def needsDoubleBond (m : Work) (wasAromatic : Nat → Bool) (ev0 : Nat) (i : Nat) : Bool := Id.run do
  let a := m.atoms[i]!
  let z := a.z
  let totH := a.explicitHs + a.cachedImplicit
  let impl : Int := a.cachedImplicit
  -- aromatic bonds count 1 each, others their (rounded) order
  let mut sbo : Int := totH
  for k in m.bondsOf i do
    let o := m.bonds[k]!.kind
    sbo := sbo + (if wasAromatic k then 1 else ((halfOrder o + 1) / 2 : Nat))
  let mut chrg : Int := a.charge
  if isEarly z then chrg := -chrg
  if z == 6 && 0 < chrg then chrg := -chrg
  let mut dv : Int := defaultValence z + chrg
  let tbo : Int := ev0 + impl
  let nrad : Int := a.radicals
  let tdeg : Int := m.degree i + impl
  -- move up the allowed-valence list while the atom is over-valent
  for v in (valences z).drop 1 do
    if dv < tbo && 0 < v then dv := v + chrg
  -- aromatic N-oxide (Kekulize.cpp:176)
  if tbo == 5 && sbo == 4 && dv == 3 && tdeg == 3 && nrad == 0 && chrg == 0 &&
      totH == 0 && [7, 15, 33].contains z then
    dv := 5
  if dv ≤ tdeg + nrad then return false
  return dv == sbo + 1 + nrad || (nrad == 0 && a.noImplicit && dv == sbo + 2)

/-- The state of `kekulizeWorker`'s walk: RDKit's local variables. -/
structure KekState where
  /-- The molecule, with the double bonds placed so far. -/
  m : Work
  /-- The atoms that still need a double bond. -/
  cands : Array Bool
  /-- The atoms visited, in order. -/
  done : List Nat
  /-- The bonds the walk has made double. -/
  adds : Array Bool
  /-- The atoms to visit next. -/
  queue : List Nat
  /-- Atom ↦ the neighbours not yet tried as its double-bond partner. -/
  options : List (Nat × List Nat)
  /-- The atom to back-track to. -/
  lastOpt : Option Nat
  /-- The atoms with untried options, oldest first. -/
  btMoves : List Nat
  /-- Back-tracks so far. -/
  numBt : Nat

/-- The atom the walk visits next, with the queue after it: the queue's head, else the lowest
atom of `sorted` not done yet (with an empty queue); `none` when every atom is done. -/
def KekState.nextAtom (s : KekState) (sorted : List Nat) : Option (Nat × List Nat) :=
  match s.queue with
  | c :: rest => some (c, rest)
  | [] => (sorted.find? (!s.done.contains ·)).map (·, [])

/-- One neighbour `j` of `curr` in the scan: `j` joins the new queue unless it is queued, and it
is an option for `curr`'s double bond if both need one and their bond was written aromatic.
The accumulator is (new queue, options). -/
def scanStep (m : Work) (wasAromatic : Nat → Bool) (cands : Array Bool) (curr : Nat)
    (ccand : Bool) (queue : List Nat) (p : List Nat × List Nat) (j : Nat) :
    List Nat × List Nat :=
  let newQueue := if !queue.contains j then p.1 ++ [j] else p.1
  let opts := match m.bondBetween? curr j with
    | some k => if ccand && cands[j]! && wasAromatic k then p.2 ++ [j] else p.2
    | none => p.2
  (newQueue, opts)

/-- Bond `k` in a back-track: a bond the walk made double, with neither end in `keep`, is made
single again and its ends need a double bond again. The accumulator is (molecule, bonds made
double, atoms needing one). -/
def undoAdds (keep : List Nat) (p : Work × Array Bool × Array Bool) (k : Nat) :
    Work × Array Bool × Array Bool :=
  let (m, adds, cands) := p
  if adds[k]! then
    let b := m.bonds[k]!
    if !keep.contains b.src && !keep.contains b.dst then
      (m.setKind k .single, adds.set! k false, (cands.set! b.src true).set! b.dst true)
    else p
  else p

/-- `curr` gets its double bond, along bond `k` to its first option `n`; `rest` are its other
options, kept for back-tracking. -/
def KekState.placeDouble (s : KekState) (curr n k : Nat) (rest : List Nat) : KekState :=
  let (options, btMoves, lastOpt) :=
    if (s.options.lookup curr).isSome then
      if rest.isEmpty then
        (s.options.filter (·.1 != curr), s.btMoves.dropLast, s.btMoves.dropLast.getLast?)
      else
        (s.options.map fun (a, o) ↦ if a == curr then (a, rest) else (a, o), s.btMoves,
          s.lastOpt)
    else if !rest.isEmpty then (s.options ++ [(curr, rest)], s.btMoves ++ [curr], some curr)
    else (s.options, s.btMoves, s.lastOpt)
  { s with m := s.m.setKind k .double, cands := (s.cands.set! curr false).set! n false,
           adds := s.adds.set! k true, options, btMoves, lastOpt }

/-- Back-track to `lo` (`backTrack`, `Kekulize.cpp:24`): the atoms done from `lo` on go back to
the head of the queue, and the double bonds placed away from the atoms kept are undone. -/
def KekState.backTrack (s : KekState) (lo : Nat) : KekState :=
  let pos := s.done.idxOf lo
  let keep := s.done.take pos
  let (m, adds, cands) := (List.range s.m.numBonds).foldl (undoAdds keep) (s.m, s.adds, s.cands)
  { s with m, adds, cands, queue := s.done.drop pos ++ s.queue, done := keep,
           numBt := s.numBt + 1 }

/-- One pass of `kekulizeWorker`'s walk: visit the next atom, give it a double bond if it needs
one, or back-track. `.inl r` ends the walk with `r`; `.inr s` goes on from `s`. `atoms` are the
system's atoms and `sorted` the same in increasing order. -/
def kekulizeStep (wasAromatic : Nat → Bool) (atoms sorted : List Nat) (s : KekState) :
    Option Work ⊕ KekState :=
  match s.nextAtom sorted with
  | none => .inl (some s.m)
  | some (curr, queue) =>
    let done := s.done ++ [curr]
    let ccand := s.cands[curr]!
    -- options for `curr`'s double bond: kept from an earlier visit, else from scanning its
    -- neighbours, which also queues them
    let (opts, queue) := match s.options.lookup curr with
      | some o => (o, queue)
      | none =>
        let nbrs := ((s.m.neighbors curr).map (·.2)).filter fun j ↦
          atoms.contains j && !done.contains j
        let p := (nbrs.mergeSort (· ≤ ·)).foldl
          (scanStep s.m wasAromatic s.cands curr ccand queue) ([], [])
        (p.2, queue ++ p.1)
    let s := { s with done, queue }
    if !ccand then .inr s else
    match opts with
    | n :: rest =>
      match s.m.bondBetween? curr n with
      | some k => .inr (s.placeDouble curr n k rest)
      | none => .inl none
    | [] =>
      -- stuck: back to the last atom that still has options
      match s.lastOpt with
      | some lo => if 100 ≤ s.numBt then .inl none else .inr (s.backTrack lo)
      | none => .inl none

/-- `kekulizeWorker`'s walk, at most `fuel` passes: it goes on while some atom of the system is
not done or the queue is not empty. Out of fuel, it fails. -/
def kekulizeLoop (wasAromatic : Nat → Bool) (atoms sorted : List Nat) :
    Nat → KekState → Option Work
  | 0, _ => none
  | fuel + 1, s =>
    if s.done.length < sorted.length || !s.queue.isEmpty then
      match kekulizeStep wasAromatic atoms sorted s with
      | .inl r => r
      | .inr s' => kekulizeLoop wasAromatic atoms sorted fuel s'
    else some s.m

/-- Passes enough for any walk over `atoms`: a back-track at most doubles the visited atoms and
the queue, and there are at most 100 back-tracks. (RDKit writes the walk as a `while` loop; the
bound makes it a structural recursion, so that what it returns can be proved.) -/
def kekulizeFuel (atoms : List Nat) : Nat := (atoms.length + 1) * 2 ^ 110

/-- RDKit's `kekulizeWorker` for one fused system: `atoms` are its atoms, `cands`
marks the atoms that need a double bond, `done` starts with its non-aromatic
atoms. Returns the molecule with double bonds placed, or `none` if impossible. -/
def kekulizeWorker (m : Work) (wasAromatic : Nat → Bool) (atoms : List Nat) (cands : Array Bool)
    (done : List Nat) : Option Work :=
  kekulizeLoop wasAromatic atoms (atoms.mergeSort (· ≤ ·)) (kekulizeFuel atoms)
    { m, cands, done, adds := Array.replicate m.numBonds false, queue := [], options := [],
      lastOpt := none, btMoves := [], numBt := 0 }

/-- The aromatic bonds of aromatic atom `i` become single (`markDbondCands`). -/
def singleAromaticBonds (wasAromatic : Nat → Bool) (out : Work) (i : Nat) : Work :=
  if out.atoms[i]!.aromatic then
    (out.bondsOf i).foldl (fun o k ↦ if wasAromatic k then o.setKind k .single else o) out
  else out

/-- One fused ring system `system` (indices into `rings`) of `Kekulize`: if any of its atoms is
aromatic, mark the atoms that need a double bond, make the aromatic bonds of its aromatic atoms
single, and place the double bonds with `kekulizeWorker`. `ev0` are the explicit valences before
kekulization. -/
def kekulizeSystem (wasAromatic : Nat → Bool) (ev0 : List Nat) (rings : Array (List Nat))
    (out : Work) (system : List Nat) : Except String Work :=
  let atoms := (system.flatMap (rings[·]!)).eraseDups
  if !atoms.any (out.atoms[·]!.aromatic) then pure out else
  -- markDbondCands: candidates, non-aromatic atoms are already done,
  -- aromatic bonds of the aromatic atoms become single
  let cands := atoms.foldl (init := Array.replicate out.numAtoms false) fun c i ↦
    if out.atoms[i]!.aromatic && out.needsDoubleBond wasAromatic ev0[i]! i then c.set! i true
    else c
  let done := atoms.filter (!out.atoms[·]!.aromatic)
  match (atoms.foldl (singleAromaticBonds wasAromatic) out).kekulizeWorker wasAromatic atoms
    cands done with
  | some m' => pure m'
  | none => throw "Can't kekulize mol"

/-- Clear atom `i`'s aromatic flag (`markAtomsBonds`); an aromatic atom outside every ring is an
error. GitHub #141: a neutral aromatic N/P with one bracket H keeps the H implicitly, and RDKit
refreshes its cached valence on the Kekulé graph (`Kekulize.cpp:789`). -/
def clearAromatic (ringAtoms : List Nat) (out : Work) (i : Nat) : Except String Work :=
  let a := out.atoms[i]!
  if !a.aromatic then pure out
  else if !ringAtoms.contains i then throw s!"non-ring atom {i} marked aromatic"
  else if [7, 15].contains a.z && a.charge == 0 && a.explicitHs == 1 then
    let ev := ((out.bondsOf i).foldl (fun s k ↦ s + halfOrder out.bonds[k]!.kind) 0) / 2
    let out := out.modifyAtom i fun a ↦
      { a with aromatic := false, noImplicit := false, explicitHs := 0, cachedValence := some ev }
    pure (out.modifyAtom i ({ · with cachedImplicit := out.implicitHs i }))
  else pure (out.modifyAtom i ({ · with aromatic := false }))

/-- RDKit's `Kekulize` (`KekulizeFragment` with `canonical = false`) over the fused ring systems
of `rings`; fails (like RDKit's "Can't kekulize mol") if no valid structure exists. -/
def kekulize (m : Work) (rings : Array (List Nat)) : Except String Work := do
  let aromaticBonds := (List.range m.numBonds).filter (m.bonds[·]!.kind == .aromatic)
  if aromaticBonds.isEmpty && !m.atoms.any (·.aromatic) then return m
  let wasAromatic (k : Nat) : Bool := aromaticBonds.contains k
  let ev0 := (List.range m.numAtoms).map m.explicitValence
  -- fused systems: rings sharing at least one bond (Kekulize.cpp:727-746)
  let rbonds := rings.map m.ringBonds
  let nbrs := (List.range rings.size).toArray.map fun i ↦
    (List.range rings.size).filter fun j ↦
      j != i && rbonds[i]!.any rbonds[j]!.contains
  let out ← (components rings.size nbrs).foldlM (kekulizeSystem wasAromatic ev0 rings) m
  -- markAtomsBonds: clear aromatic flags
  let out ← (List.range out.numAtoms).foldlM (clearAromatic rings.toList.flatten.eraseDups) out
  if out.bonds.any (·.kind == .aromatic) then throw "aromatic bond left after kekulization"
  return out

end Work
end LeanSMILES.Aromaticity
