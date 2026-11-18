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

Method (Vismara 1997), ported from `tools/rdkit_reference/aromaticity_ref.py`
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

/-- Number of set bits of `n`: the size (bond count) of a cycle stored as a bond bitmask. -/
def popcount (n : Nat) : Nat := (List.range (n.log2 + 1)).countP n.testBit

/-- Lexicographic order on lists of atom indices, as a `Bool`; `Work.relevantCycles` uses it to
order same-size cycles by their sorted atoms. -/
def listLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && listLt as bs)

/-- One visit of the breadth-first search: each neighbour of `u` not reached yet gets `u`'s
distance plus one and joins the end of the queue. -/
def Work.bfsVisit (m : Work) (u : Nat) (p : Array (Option Nat) × Array Nat) :
    Array (Option Nat) × Array Nat :=
  let du := (p.1[u]!).getD 0
  (m.neighbors u).foldl (fun (dist, queue) (_, v) ↦
    if dist[v]!.isNone then (dist.set! v (some (du + 1)), queue.push v) else (dist, queue)) p

/-- The breadth-first search from queue position `head`, at most `fuel` visits. -/
def Work.bfsLoop (m : Work) : Nat → Nat → Array (Option Nat) × Array Nat →
    Array (Option Nat) × Array Nat
  | 0, _, p => p
  | fuel + 1, head, p =>
    if h : head < p.2.size then m.bfsLoop fuel (head + 1) (m.bfsVisit p.2[head] p) else p

/-- Breadth-first distances from `r` (`none` = unreachable) and the visiting order, which lists the
reachable atoms by nondecreasing distance (`_bfs` in `aromaticity_ref.py`). Each atom is queued
once, so `numAtoms + 1` visits suffice for a well-formed copy. (RDKit's search is a `while` loop;
written with a bound it is a structural recursion, so that what it returns can be proved.) -/
def Work.bfs (m : Work) (r : Nat) : Array (Option Nat) × Array Nat :=
  m.bfsLoop (m.numAtoms + m.numBonds + 2) 0
    ((Array.replicate m.numAtoms none).set! r (some 0), #[r])

/-- The search reads the copy only through its neighbour lists and sizes. -/
lemma Work.bfs_congr {w w' : Work} (hn : w'.neighbors = w.neighbors)
    (ha : w'.numAtoms = w.numAtoms) (hb : w'.numBonds = w.numBonds) : w'.bfs = w.bfs := by
  have hv : w'.bfsVisit = w.bfsVisit := by
    funext u p
    simp only [Work.bfsVisit, hn]
  have hl : w'.bfsLoop = w.bfsLoop := by
    funext fuel
    induction fuel with
    | zero => rfl
    | succ n ih =>
      funext head p
      simp only [Work.bfsLoop, hv, ih]
  funext r
  simp only [Work.bfs, hl, ha, hb]

/-- Every shortest path from `r` to each atom, as atom lists starting at `r`, filled along the BFS
`order` so each atom's predecessors come first (`_all_shortest_paths` in `aromaticity_ref.py`). -/
def Work.allShortestPaths (m : Work) (dist : Array (Option Nat)) (order : Array Nat) (r : Nat) :
    Array (List (List Nat)) := Id.run do
  let mut paths : Array (List (List Nat)) := (Array.replicate m.numAtoms []).set! r [[r]]
  for v in order do
    if v == r then continue
    let dv := (dist[v]!).getD 0
    let preds := (m.neighbors v).filterMap fun (_, u) ↦
      if dist[u]! == some (dv - 1) then some u else none
    paths := paths.set! v (preds.flatMap fun u ↦ paths[u]!.map (· ++ [v]))
  return paths

/-- Bond bitmask of a cycle given as a list of atoms: bit `k` is set iff bond `k` joins two
consecutive atoms of the cycle (the `mask` of `add` in `relevant_cycles`). -/
def Work.cycleMask (m : Work) (cyc : List Nat) : Nat :=
  let n := cyc.length
  (List.range n).foldl (init := 0) fun acc t ↦
    match m.bondBetween? (cyc[t]!) (cyc[(t + 1) % n]!) with
    | some k => acc ||| (1 <<< k)
    | none => acc

/-- Candidate cycles (bond mask, atoms), first representative of each bond set kept: for each root,
two vertex-disjoint shortest paths closed by a bond or by a shared atom (`relevant_cycles`). -/
def Work.candidateCycles (m : Work) : Array (Nat × List Nat) := Id.run do
  let mut cands : Array (Nat × List Nat) := #[]
  let disjointTails (p q : List Nat) := p.tail.all fun a ↦ !q.tail.contains a
  for r in [0:m.numAtoms] do
    let (dist, order) := m.bfs r
    let paths := m.allShortestPaths dist order r
    let mut found : List (List Nat) := []
    for x in [0:m.numAtoms] do
      let some dx := dist[x]! | continue
      if dx == 0 then continue
      -- odd cycles: bond x–y with both ends at the same distance
      for (_, y) in m.neighbors x do
        if x < y && dist[y]! == some dx then
          for p in paths[x]! do
            for q in paths[y]! do
              if disjointTails p q then found := found ++ [p ++ q.reverse.dropLast]
      -- even cycles: x reached by two different predecessors
      if 2 ≤ dx then
        let preds := (m.neighbors x).filterMap fun (_, u) ↦
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

/-- Reduce bitmask `v` by a GF(2) echelon basis of (pivot bit, vector) pairs, highest pivot first
(`reduce` in `relevant_cycles`); `v` reduces to `0` iff it is a sum of basis vectors. -/
def reduceBy (basis : List (Nat × Nat)) (v : Nat) : Nat :=
  basis.foldl (init := v) fun v (p, b) ↦ if v.testBit p then v ^^^ b else v

/-- RDKit's ring set (`symmetrizeSSSR`, `FindRings.cpp:1085`): the relevant cycles as atom lists,
sorted by (size, sorted atoms), following `relevant_cycles` in `aromaticity_ref.py`. -/
def Work.relevantCycles (m : Work) : Array (List Nat) := Id.run do
  let key (c : Nat × List Nat) := (popcount c.1, c.2.mergeSort (· ≤ ·))
  let sorted := m.candidateCycles.toList.mergeSort fun a b ↦
    let (la, sa) := key a
    let (lb, sb) := key b
    la < lb || (la == lb && (listLt sa sb || sa == sb))
  let sizes := (sorted.map (popcount ·.1)).eraseDups
  let mut basis : List (Nat × Nat) := []
  let mut result : Array (List Nat) := #[]
  for size in sizes do
    let group := sorted.filter (popcount ·.1 == size)
    -- independent of the strictly smaller cycles kept so far?
    let kept := group.filter fun c ↦ reduceBy basis c.1 != 0
    result := result ++ (kept.map (·.2)).toArray
    for c in kept do
      let v := reduceBy basis c.1
      if v != 0 then
        basis := (basis ++ [(v.log2, v)]).mergeSort fun x y ↦ y.1 ≤ x.1
  return result

/-- Connected components of a graph on `[0, n)` given by neighbor lists, each sorted increasingly;
`Kekulize` groups fused ring systems with it (`RingUtils::pickFusedRings`). -/
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

/-- One sweep over the bonds other than `skip`: a bond with one endpoint marked marks the other. -/
def Work.reachSweep (m : Work) (skip : Nat) (seen : Array Bool) : Array Bool :=
  (List.range m.numBonds).foldl (init := seen) fun seen k ↦
    if k == skip then seen else
    let b := m.bonds[k]!
    if seen[b.src]! && !seen[b.dst]! then seen.set! b.dst true
    else if seen[b.dst]! && !seen[b.src]! then seen.set! b.src true
    else seen

/-- Is bond `k` on a cycle: are its endpoints still joined without it? `numAtoms` sweeps from
one endpoint reach everything reachable. This is RDKit's "is the bond in a ring of the ring set"
(`numBondRings`): the relevant cycles span the cycle space, so every bond on a cycle lies on a
relevant cycle. -/
def Work.onCycle (m : Work) (k : Nat) : Bool :=
  let b := m.bonds[k]!
  ((m.reachSweep k)^[m.numAtoms] ((Array.replicate m.numAtoms false).set! b.src true))[b.dst]!

/-- Bond indices around a ring given as atoms, in ring order (`RingUtils::convertToBonds`). -/
def Work.ringBonds (m : Work) (ring : List Nat) : List Nat :=
  let n := ring.length
  (List.range n).filterMap fun t ↦ m.bondBetween? (ring[t]!) (ring[(t + 1) % n]!)

end LeanSMILES.Aromaticity
