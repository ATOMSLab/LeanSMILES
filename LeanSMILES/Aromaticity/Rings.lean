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
@[irreducible] def Work.bfs (m : Work) (r : Nat) : Array (Option Nat) × Array Nat :=
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

/-- The predecessors of atom `v` on shortest paths: its neighbours one step nearer the root. -/
def Work.shortestPreds (m : Work) (dist : Array (Option Nat)) (v : Nat) : List Nat :=
  let dv := (dist[v]!).getD 0
  (m.neighbors v).filterMap fun (_, u) ↦ if dist[u]! == some (dv - 1) then some u else none

/-- One atom of `allShortestPaths`: the paths to `v` are those to its predecessors, extended by
`v`. -/
def Work.shortestPathsStep (m : Work) (dist : Array (Option Nat)) (r : Nat)
    (paths : Array (List (List Nat))) (v : Nat) : Array (List (List Nat)) :=
  if v == r then paths
  else paths.set! v ((m.shortestPreds dist v).flatMap fun u ↦ paths[u]!.map (· ++ [v]))

/-- Every shortest path from `r` to each atom, as atom lists starting at `r`, filled along the BFS
`order` so each atom's predecessors come first (`_all_shortest_paths` in `aromaticity_ref.py`). -/
def Work.allShortestPaths (m : Work) (dist : Array (Option Nat)) (order : Array Nat) (r : Nat) :
    Array (List (List Nat)) :=
  order.toList.foldl (m.shortestPathsStep dist r) ((Array.replicate m.numAtoms []).set! r [[r]])

/-- Bond bitmask of a cycle given as a list of atoms: bit `k` is set iff bond `k` joins two
consecutive atoms of the cycle (the `mask` of `add` in `relevant_cycles`). -/
def Work.cycleMask (m : Work) (cyc : List Nat) : Nat :=
  let n := cyc.length
  (List.range n).foldl (init := 0) fun acc t ↦
    match m.bondBetween? (cyc[t]!) (cyc[(t + 1) % n]!) with
    | some k => acc ||| (1 <<< k)
    | none => acc

/-- Two paths from the root that meet only there. -/
def disjointTails (p q : List Nat) : Bool := p.tail.all fun a ↦ !q.tail.contains a

/-- Odd cycles through the bond from `x` (at distance `dx`) to a later neighbour at the same
distance: a shortest path to each end, closed by the bond. -/
def Work.oddCycles (m : Work) (dist : Array (Option Nat)) (paths : Array (List (List Nat)))
    (x dx : Nat) : List (List Nat) :=
  (m.neighbors x).flatMap fun (_, y) ↦
    if x < y && dist[y]! == some dx then
      paths[x]!.flatMap fun p ↦ paths[y]!.filterMap fun q ↦
        if disjointTails p q then some (p ++ q.reverse.dropLast) else none
    else []

/-- Even cycles at `x` (at distance `dx`): shortest paths to two different predecessors, closed
through `x`. -/
def Work.evenCycles (m : Work) (dist : Array (Option Nat)) (paths : Array (List (List Nat)))
    (x dx : Nat) : List (List Nat) :=
  let preds := (m.neighbors x).filterMap fun (_, u) ↦
    if dist[u]! == some (dx - 1) then some u else none
  (List.range preds.length).flatMap fun a ↦ (List.range' (a + 1) (preds.length - (a + 1))).flatMap
    fun b ↦ paths[preds[a]!]!.flatMap fun p ↦ paths[preds[b]!]!.filterMap fun q ↦
      if disjointTails p q then some (p ++ [x] ++ q.reverse.dropLast) else none

/-- The cycles found at atom `x` for the root whose distances and paths are given. -/
def Work.cyclesAt (m : Work) (dist : Array (Option Nat)) (paths : Array (List (List Nat)))
    (x : Nat) : List (List Nat) :=
  match dist[x]! with
  | none => []
  | some dx =>
    if dx == 0 then []
    else m.oddCycles dist paths x dx ++ (if 2 ≤ dx then m.evenCycles dist paths x dx else [])

/-- The cycles found from root `r`. -/
def Work.cyclesFrom (m : Work) (r : Nat) : List (List Nat) :=
  let (dist, order) := m.bfs r
  let paths := m.allShortestPaths dist order r
  (List.range m.numAtoms).flatMap (m.cyclesAt dist paths)

/-- Keep a cycle unless one with the same bond set is kept already. -/
def Work.addCandidate (m : Work) (cands : Array (Nat × List Nat)) (cyc : List Nat) :
    Array (Nat × List Nat) :=
  let mask := m.cycleMask cyc
  if !cands.any (·.1 == mask) then cands.push (mask, cyc) else cands

/-- Candidate cycles (bond mask, atoms), first representative of each bond set kept: for each root,
two vertex-disjoint shortest paths closed by a bond or by a shared atom (`relevant_cycles`). -/
@[irreducible] def Work.candidateCycles (m : Work) : Array (Nat × List Nat) :=
  (List.range m.numAtoms).foldl (fun cands r ↦ (m.cyclesFrom r).foldl m.addCandidate cands) #[]

/-- Reduce bitmask `v` by a GF(2) echelon basis of (pivot bit, vector) pairs, highest pivot first
(`reduce` in `relevant_cycles`); `v` reduces to `0` iff it is a sum of basis vectors. -/
def reduceBy (basis : List (Nat × Nat)) (v : Nat) : Nat :=
  basis.foldl (init := v) fun v (p, b) ↦ if v.testBit p then v ^^^ b else v

/-- Add a kept cycle's reduced mask to the echelon basis, if it is not a sum of the others. -/
def addToBasis (basis : List (Nat × Nat)) (c : Nat × List Nat) : List (Nat × Nat) :=
  let v := reduceBy basis c.1
  if v != 0 then (basis ++ [(v.log2, v)]).mergeSort fun x y ↦ y.1 ≤ x.1 else basis

/-- One size of `relevantCycles`: keep the cycles of that size independent of the strictly
smaller cycles kept so far, and add them to the basis. -/
def relevantStep (sorted : List (Nat × List Nat))
    (st : List (Nat × Nat) × Array (List Nat)) (size : Nat) :
    List (Nat × Nat) × Array (List Nat) :=
  let (basis, result) := st
  let group := sorted.filter (popcount ·.1 == size)
  let kept := group.filter fun c ↦ reduceBy basis c.1 != 0
  (kept.foldl addToBasis basis, result ++ (kept.map (·.2)).toArray)

/-- RDKit's ring set (`symmetrizeSSSR`, `FindRings.cpp:1085`): the relevant cycles as atom lists,
sorted by (size, sorted atoms), following `relevant_cycles` in `aromaticity_ref.py`. -/
@[irreducible] def Work.relevantCycles (m : Work) : Array (List Nat) :=
  let key (c : Nat × List Nat) := (popcount c.1, c.2.mergeSort (· ≤ ·))
  let sorted := m.candidateCycles.toList.mergeSort fun a b ↦
    let (la, sa) := key a
    let (lb, sb) := key b
    la < lb || (la == lb && (listLt sa sb || sa == sb))
  let sizes := (sorted.map (popcount ·.1)).eraseDups
  (sizes.foldl (relevantStep sorted) ([], #[])).2

/-- **Ring perception reads the copy only through its neighbour lists, `bondBetween?` and sizes.**
-/
lemma Work.relevantCycles_congr {w w' : Work} (hn : w'.neighbors = w.neighbors)
    (hbb : w'.bondBetween? = w.bondBetween?) (ha : w'.numAtoms = w.numAtoms)
    (hb : w'.numBonds = w.numBonds) : w'.relevantCycles = w.relevantCycles := by
  have hbfs := Work.bfs_congr hn ha hb
  have hpred : w'.shortestPreds = w.shortestPreds := by
    funext d v
    simp only [Work.shortestPreds, hn]
  have hstep : w'.shortestPathsStep = w.shortestPathsStep := by
    funext d r p v
    simp only [Work.shortestPathsStep, hpred]
  have hasp : w'.allShortestPaths = w.allShortestPaths := by
    funext d o r
    simp only [Work.allShortestPaths, hstep, ha]
  have hodd : w'.oddCycles = w.oddCycles := by
    funext d p x dx
    simp only [Work.oddCycles, hn]
  have heven : w'.evenCycles = w.evenCycles := by
    funext d p x dx
    simp only [Work.evenCycles, hn]
  have hat : w'.cyclesAt = w.cyclesAt := by
    funext d p x
    simp only [Work.cyclesAt, hodd, heven]
  have hfrom : w'.cyclesFrom = w.cyclesFrom := by
    funext r
    simp only [Work.cyclesFrom, hbfs, hasp, hat, ha]
  have hmask : w'.cycleMask = w.cycleMask := by
    funext c
    simp only [Work.cycleMask, hbb]
  have hadd : w'.addCandidate = w.addCandidate := by
    funext c cyc
    simp only [Work.addCandidate, hmask]
  have hcc : w'.candidateCycles = w.candidateCycles := by
    simp only [Work.candidateCycles, hfrom, hadd, ha]
  simp only [Work.relevantCycles, hcc]

/-- One neighbour in the depth-first search: if not seen, it is marked and pushed. -/
def pushNbr (st : Array Bool × List Nat) (v : Nat) : Array Bool × List Nat :=
  if !st.1[v]! then (st.1.set! v true, v :: st.2) else st

/-- The depth-first search of one component, at most `fuel` pops: (seen, component, stack). -/
def dfsComp (nbrs : Array (List Nat)) : Nat → Array Bool × List Nat × List Nat →
    Array Bool × List Nat
  | 0, (seen, comp, _) => (seen, comp)
  | _ + 1, (seen, comp, []) => (seen, comp)
  | fuel + 1, (seen, comp, u :: rest) =>
    let (seen, stack) := nbrs[u]!.foldl pushNbr (seen, rest)
    dfsComp nbrs fuel (seen, u :: comp, stack)

/-- One start atom of `components`: if not seen, its component, sorted. -/
def componentsStep (n : Nat) (nbrs : Array (List Nat)) (st : Array Bool × List (List Nat))
    (s : Nat) : Array Bool × List (List Nat) :=
  let (seen, comps) := st
  if seen[s]! then (seen, comps) else
  let (seen, comp) := dfsComp nbrs n (seen.set! s true, [], [s])
  (seen, comps ++ [comp.mergeSort (· ≤ ·)])

/-- Connected components of a graph on `[0, n)` given by neighbor lists, each sorted increasingly;
`Kekulize` groups fused ring systems with it (`RingUtils::pickFusedRings`). The search of each
component pops at most `n` atoms, as RDKit's loop does. -/
@[irreducible] def components (n : Nat) (nbrs : Array (List Nat)) : List (List Nat) :=
  ((List.range n).foldl (componentsStep n nbrs) (Array.replicate n false, [])).2

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
