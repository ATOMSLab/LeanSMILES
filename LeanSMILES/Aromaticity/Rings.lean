/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.Basic

/-!
# LeanSMILES.Aromaticity.Rings

The ring set: relevant cycles

RDKit's ring perception in sanitization (`symmetrizeSSSR`, `FindRings.cpp:1085`,
non-legacy default) returns the **relevant cycles**: the cycles that are not a
sum (over GF(2), i.e. symmetric difference of bond sets) of strictly shorter
cycles. Kekulization and aromaticity work ring by ring over this set.

Method (Vismara 1997), ported from `docs/reference/aromaticity_ref.py`
(`relevant_cycles`): every relevant cycle is made of a root atom `r` plus two
shortest paths from `r` that only meet at `r`, closed either by a bond (odd
length) or by a shared atom (even length). We enumerate all such candidates,
sort them by size, and keep a candidate if it is independent of the cycles
kept from strictly smaller sizes. Bond sets are bitmasks (`Nat`).

Ring membership (`Molecule.inRingVector`) does not need this: it only asks
*whether* a bond is on some cycle.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- Number of set bits. -/
def popcount (n : Nat) : Nat := (List.range (n.log2 + 1)).countP n.testBit

/-- Lexicographic order on lists of atom indices. -/
def listLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && listLt as bs)

/-- Breadth-first distances from `r` (`none` = unreachable) and the visiting order. -/
def Work.bfs (m : Work) (r : Nat) : Array (Option Nat) × Array Nat := Id.run do
  let mut dist : Array (Option Nat) := (Array.replicate m.numAtoms none).set! r (some 0)
  let mut queue := #[r]
  let mut head := 0
  while h : head < queue.size do
    let u := queue[head]
    head := head + 1
    let du := (dist[u]!).getD 0
    for (_, v) in m.neighbors u do
      if dist[v]!.isNone then
        dist := dist.set! v (some (du + 1))
        queue := queue.push v
  return (dist, queue)

/-- Every shortest path from `r` to each atom, as atom lists starting at `r`. -/
def Work.allShortestPaths (m : Work) (dist : Array (Option Nat)) (order : Array Nat) (r : Nat) :
    Array (List (List Nat)) := Id.run do
  let mut paths : Array (List (List Nat)) := (Array.replicate m.numAtoms []).set! r [[r]]
  for v in order do
    if v == r then continue
    let dv := (dist[v]!).getD 0
    let preds := (m.neighbors v).filterMap fun (_, u) =>
      if dist[u]! == some (dv - 1) then some u else none
    paths := paths.set! v (preds.flatMap fun u => paths[u]!.map (· ++ [v]))
  return paths

/-- Bond bitmask of a cycle given as a list of atoms. -/
def Work.cycleMask (m : Work) (cyc : List Nat) : Nat :=
  let n := cyc.length
  (List.range n).foldl (init := 0) fun acc t =>
    match m.bondBetween? (cyc[t]!) (cyc[(t + 1) % n]!) with
    | some k => acc ||| (1 <<< k)
    | none => acc

/-- Candidate cycles (bond mask, atoms), first representative of each bond set kept. -/
def Work.candidateCycles (m : Work) : Array (Nat × List Nat) := Id.run do
  let mut cands : Array (Nat × List Nat) := #[]
  let disjointTails (p q : List Nat) := p.tail.all fun a => !q.tail.contains a
  for r in [0:m.numAtoms] do
    let (dist, order) := m.bfs r
    let paths := m.allShortestPaths dist order r
    let mut found : List (List Nat) := []
    for x in [0:m.numAtoms] do
      let some dx := dist[x]! | continue
      if dx == 0 then continue
      -- odd cycles: bond x–y with both ends at the same distance
      for (_, y) in m.neighbors x do
        if y > x && dist[y]! == some dx then
          for p in paths[x]! do
            for q in paths[y]! do
              if disjointTails p q then found := found ++ [p ++ q.reverse.dropLast]
      -- even cycles: x reached by two different predecessors
      if dx ≥ 2 then
        let preds := (m.neighbors x).filterMap fun (_, u) =>
          if dist[u]! == some (dx - 1) then some u else none
        for a in [0:preds.length] do
          for b in [a + 1:preds.length] do
            for p in paths[preds[a]!]! do
              for q in paths[preds[b]!]! do
                if disjointTails p q then found := found ++ [p ++ [x] ++ q.reverse.dropLast]
    for cyc in found do
      let mask := m.cycleMask cyc
      if !cands.any (·.1 == mask) then cands := cands.push (mask, cyc)
  return cands

/-- Reduce bitmask `v` by a GF(2) basis of (pivot bit, vector), highest pivot first. -/
def reduceBy (basis : List (Nat × Nat)) (v : Nat) : Nat :=
  basis.foldl (init := v) fun v (p, b) => if v.testBit p then v ^^^ b else v

/-- RDKit's ring set: the relevant cycles, as atom lists, sorted by
(size, sorted atoms). -/
def Work.relevantCycles (m : Work) : Array (List Nat) := Id.run do
  let key (c : Nat × List Nat) := (popcount c.1, c.2.mergeSort (· ≤ ·))
  let sorted := m.candidateCycles.toList.mergeSort fun a b =>
    let (la, sa) := key a
    let (lb, sb) := key b
    la < lb || (la == lb && (listLt sa sb || sa == sb))
  let sizes := (sorted.map (popcount ·.1)).eraseDups
  let mut basis : List (Nat × Nat) := []
  let mut result : Array (List Nat) := #[]
  for size in sizes do
    let group := sorted.filter (popcount ·.1 == size)
    -- independent of the strictly smaller cycles kept so far?
    let kept := group.filter fun c => reduceBy basis c.1 != 0
    result := result ++ (kept.map (·.2)).toArray
    for c in kept do
      let v := reduceBy basis c.1
      if v != 0 then
        basis := (basis ++ [(v.log2, v)]).mergeSort fun x y => x.1 ≥ y.1
  return result

/-- Connected components of a graph on `[0, n)` given by neighbour lists. -/
def components (n : Nat) (nbrs : Array (List Nat)) : List (List Nat) := Id.run do
  let mut seen := Array.replicate n false
  let mut comps : List (List Nat) := []
  for s in [0:n] do
    if seen[s]! then continue
    seen := seen.set! s true
    let mut comp : List Nat := []
    let mut stack := [s]
    for _ in [0:n] do
      match stack with
      | [] => break
      | u :: rest =>
        stack := rest
        comp := u :: comp
        for v in nbrs[u]! do
          if !seen[v]! then
            seen := seen.set! v true
            stack := v :: stack
    comps := comps ++ [comp.mergeSort (· ≤ ·)]
  return comps

/-- Bond indices around a ring given as atoms. -/
def Work.ringBonds (m : Work) (ring : List Nat) : List Nat :=
  let n := ring.length
  (List.range n).filterMap fun t => m.bondBetween? (ring[t]!) (ring[(t + 1) % n]!)

end LeanSMILES.Aromaticity
