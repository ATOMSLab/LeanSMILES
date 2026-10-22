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
`docs/reference/aromaticity_ref.py` (`kekulize`).

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
  if z == 6 && chrg > 0 then chrg := -chrg
  let mut dv : Int := defaultValence z + chrg
  let tbo : Int := ev0 + impl
  let nrad : Int := a.radicals
  let tdeg : Int := m.degree i + impl
  -- move up the allowed-valence list while the atom is over-valent
  for v in (valences z).drop 1 do
    if tbo > dv && v > 0 then dv := v + chrg
  -- aromatic N-oxide (Kekulize.cpp:176)
  if tbo == 5 && sbo == 4 && dv == 3 && tdeg == 3 && nrad == 0 && chrg == 0 &&
      totH == 0 && [7, 15, 33].contains z then
    dv := 5
  if tdeg + nrad ≥ dv then return false
  return dv == sbo + 1 + nrad || (nrad == 0 && a.noImplicit && dv == sbo + 2)

/-- RDKit's `kekulizeWorker` for one fused system: `atoms` are its atoms, `cands`
marks the atoms that need a double bond, `done` starts with its non-aromatic
atoms. Returns the molecule with double bonds placed, or `none` if impossible. -/
def kekulizeWorker (m : Work) (wasAromatic : Nat → Bool) (atoms : List Nat)
    (cands : Array Bool) (done : List Nat) : Option Work := Id.run do
  let mut m := m
  let mut cands := cands
  let mut done := done
  let mut adds := Array.replicate m.numBonds false
  let mut localAdded := Array.replicate m.numBonds false
  let sorted := atoms.mergeSort (· ≤ ·)
  let mut queue : List Nat := []
  let mut options : List (Nat × List Nat) := []   -- atom ↦ untried neighbours
  let mut lastOpt : Option Nat := none
  let mut btMoves : List Nat := []                 -- atoms with untried options, oldest first
  let mut numBt := 0
  while done.length < sorted.length || !queue.isEmpty do
    -- next atom: from the queue, else the lowest atom not done yet
    let curr ← match queue with
      | c :: rest => do queue := rest; pure c
      | [] => match sorted.find? (!done.contains ·) with
        | some c => pure c
        | none => return some m
    done := done ++ [curr]
    let ccand := cands[curr]!
    let mut opts : List Nat := []
    match options.lookup curr with
    | some o => opts := o
    | none =>
      let nbrs := ((m.neighbors curr).map (·.2)).filter fun j =>
        atoms.contains j && !done.contains j
      let mut newQueue : List Nat := []
      for j in nbrs.mergeSort (· ≤ ·) do
        if !queue.contains j then newQueue := newQueue ++ [j]
        if let some k := m.bondBetween? curr j then
          if ccand && cands[j]! && wasAromatic k then opts := opts ++ [j]
      queue := queue ++ newQueue
    if !ccand then continue
    match opts with
    | n :: rest =>
      -- double bond to the first option
      let some k := m.bondBetween? curr n | return none
      m := m.setKind k .double
      cands := (cands.set! curr false).set! n false
      adds := adds.set! k true
      localAdded := localAdded.set! k true
      if (options.lookup curr).isSome then
        if rest.isEmpty then
          options := options.filter (·.1 != curr)
          btMoves := btMoves.dropLast
          lastOpt := btMoves.getLast?
        else
          options := options.map fun (a, o) => if a == curr then (a, rest) else (a, o)
      else if !rest.isEmpty then
        lastOpt := some curr
        btMoves := btMoves ++ [curr]
        options := options ++ [(curr, rest)]
    | [] =>
      -- stuck: back to the last atom that still has options (backTrack, Kekulize.cpp:24)
      match lastOpt with
      | some lo =>
        if numBt ≥ 100 then return none
        numBt := numBt + 1
        let pos := done.idxOf lo
        let keep := done.take pos
        queue := done.drop pos ++ queue
        for k in [0:m.numBonds] do
          if adds[k]! then
            let b := m.bonds[k]!
            if !keep.contains b.src && !keep.contains b.dst then
              adds := adds.set! k false
              m := m.setKind k .single
              cands := (cands.set! b.src true).set! b.dst true
        done := keep
      | none => return none
  return some m

/-- Kekulize; fails (like RDKit's "Can't kekulize mol") if no valid structure exists. -/
def kekulize (m : Work) (rings : Array (List Nat)) : Except String Work := do
  let aromaticBonds := (List.range m.numBonds).filter (m.bonds[·]!.kind == .aromatic)
  if aromaticBonds.isEmpty && !m.atoms.any (·.aromatic) then return m
  let wasAromatic (k : Nat) : Bool := aromaticBonds.contains k
  let ev0 := (List.range m.numAtoms).map m.explicitValence
  -- fused systems: rings sharing at least one bond (Kekulize.cpp:727-746)
  let rbonds := rings.map m.ringBonds
  let nbrs := (List.range rings.size).toArray.map fun i =>
    (List.range rings.size).filter fun j =>
      j != i && rbonds[i]!.any rbonds[j]!.contains
  let mut out := m
  for system in components rings.size nbrs do
    let atoms := (system.flatMap (rings[·]!)).eraseDups
    if !atoms.any (out.atoms[·]!.aromatic) then continue
    -- markDbondCands: candidates, non-aromatic atoms are already done,
    -- aromatic bonds of the aromatic atoms become single
    let cands := atoms.foldl (init := Array.replicate out.numAtoms false) fun c i =>
      if out.atoms[i]!.aromatic && out.needsDoubleBond wasAromatic ev0[i]! i then c.set! i true
      else c
    let done := atoms.filter (!out.atoms[·]!.aromatic)
    for i in atoms do
      if out.atoms[i]!.aromatic then
        for k in out.bondsOf i do
          if wasAromatic k then out := out.setKind k .single
    match out.kekulizeWorker wasAromatic atoms cands done with
    | some m' => out := m'
    | none => throw "Can't kekulize mol"
  -- markAtomsBonds: clear aromatic flags
  let ringAtoms := rings.toList.flatten.eraseDups
  for i in [0:out.numAtoms] do
    let a := out.atoms[i]!
    if a.aromatic then
      if !ringAtoms.contains i then throw s!"non-ring atom {i} marked aromatic"
      -- GitHub #141: a neutral aromatic N/P with one bracket H keeps the H implicitly,
      -- and RDKit refreshes its cached valence on the Kekulé graph (Kekulize.cpp:789)
      if [7, 15].contains a.z && a.charge == 0 && a.explicitHs == 1 then
        let ev := ((out.bondsOf i).foldl (fun s k => s + halfOrder out.bonds[k]!.kind) 0) / 2
        out := out.modifyAtom i fun a =>
          { a with aromatic := false, noImplicit := false, explicitHs := 0,
                   cachedValence := some ev }
        out := out.modifyAtom i ({ · with cachedImplicit := out.implicitHs i })
      else
        out := out.modifyAtom i ({ · with aromatic := false })
  if out.bonds.any (·.kind == .aromatic) then throw "aromatic bond left after kekulization"
  return out

end Work
end LeanSMILES.Aromaticity
