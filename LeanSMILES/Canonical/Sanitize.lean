import LeanSMILES.Canonical.Parse

/-!
# LeanSMILES.Canonical.Sanitize

RDKit's sanitization: hydrogens, ring membership, cleanup, valence checks,
ring set, kekulization and aromaticity. Entry point: `Chem.molFromSmiles`.
-/

/-!
# Implicit hydrogens

A port of RDKit's `calculateExplicitValence` / `calculateImplicitValence`
(`Code/GraphMol/Atom.cpp:350-613`, Release_2026_09_1), restricted to what our
molecules can contain (no radicals, dative bonds or query bonds).

All bond orders are counted in half-units so aromatic bonds (1.5) stay exact.
-/

namespace Chem
namespace Mol

/-- RDKit's `isAromaticAtom`: lowercase, or touching an aromatic bond. -/
def isAromaticAtom (m : Mol) (i : Nat) : Bool :=
  m.atoms[i]!.aromatic || (m.bondsOf i).any fun k => m.bonds[k]!.order == .aromatic

/-- RDKit's effective atomic number: charged atoms take the valences of the
isoelectronic element (N⁺ behaves like C, O⁻ like F). -/
def effectiveAtomicNum (a : Atom) : Nat := (a.atomicNum - a.charge).toNat

/-- P, S (and As, Se) with a negative charge keep their own valence list. -/
private def canBeHypervalent (a : Atom) (eff : Nat) : Bool :=
  (eff > 16 && (a.atomicNum == 15 || a.atomicNum == 16)) ||
  (eff > 34 && (a.atomicNum == 33 || a.atomicNum == 34))

/-- RDKit's explicit valence: sum of bond orders plus explicit Hs, with the
aromatic adjustment and the "round x.5 up" rule (`Atom.cpp:350-415`). -/
def explicitValence (m : Mol) (i : Nat) : Nat := Id.run do
  let a := m.atoms[i]!
  let mut accum := 2 * a.explicitHs
  for k in m.bondsOf i do
    accum := accum + m.bonds[k]!.order.halfValence
  let valens := valences (effectiveAtomicNum a)
  if let some dv := valens.head? then
    if accum > 2 * dv && m.isAromaticAtom i then
      -- largest allowed valence not above accum; snap to it if within 1.5
      let pval := (valens.filter (2 * · ≤ accum)).getLast?.getD dv
      if accum ≤ 2 * pval + 3 then accum := 2 * pval
  return (accum + 1) / 2

/-- Number of implicit hydrogens on atom `i` (`Atom.cpp:458-613`). -/
def implicitHs (m : Mol) (i : Nat) : Nat := Id.run do
  let a := m.atoms[i]!
  if a.noImplicit then return 0
  let mut eff := effectiveAtomicNum a
  let mut ev : Int := m.explicitValence i
  if canBeHypervalent a eff then
    eff := a.atomicNum
    ev := ev - a.charge
  let valens := valences eff
  let some dv := valens.head? | return 0
  if m.isAromaticAtom i then
    return if ev ≤ dv then (dv - ev).toNat else 0
  match (valens.map Int.ofNat).find? (ev ≤ ·) with
  | some v => return (v - ev).toNat
  | none => return 0

/-- RDKit's strict valence check for atom `i` (`updatePropertyCache(strict=true)`):
an error message if the atom has more bonds than any allowed valence, as in
`FCl(F)(F)(F)F`. Ports the `strict` branches of `Atom.cpp:417-450` (explicit
valence) and `Atom.cpp:549-612` (implicit valence). -/
def valenceError? (m : Mol) (i : Nat) : Option String := Id.run do
  let a := m.atoms[i]!
  let ev : Int := m.explicitValence i
  let eff := effectiveAtomicNum a
  let some maxV := (valences eff).getLast? | return none   -- unknown element: anything goes
  -- explicit valence above the largest allowed valence
  let mut maxV : Int := maxV
  let mut offset : Int := 0
  if canBeHypervalent a eff then
    maxV := ((valences a.atomicNum).getLast?.getD 0 : Nat)
    offset := -a.charge
  if a.atomicNum == 1 && a.charge == -1 then maxV := 2
  if ev + offset > maxV then
    return some s!"Explicit valence for atom # {i} {symbol a.atomicNum}, {ev}, is greater than permitted"
  -- aromatic atoms above their default valence must sit exactly on an allowed one
  if a.noImplicit then return none
  let (eff', ev') := if canBeHypervalent a eff then (a.atomicNum, ev - a.charge) else (eff, ev)
  let valens := (valences eff').map Int.ofNat
  let some dv := valens.head? | return none
  if m.isAromaticAtom i then
    if ev' > dv && !valens.contains ev' then
      return some s!"Explicit valence for aromatic atom # {i} not equal to any accepted valence"
  else if !valens.any (ev' ≤ ·) && (valences a.atomicNum).getLast?.getD 0 > 0 then
    return some s!"Explicit valence for atom # {i} {symbol a.atomicNum} greater than permitted"
  return none

/-- The strict valence check over all atoms. -/
def checkValences (m : Mol) : Except String Unit :=
  match (List.range m.numAtoms).findSome? m.valenceError? with
  | some e => throw e
  | none => pure ()

/-- Total hydrogen count: the frozen value if set, else explicit plus implicit. -/
def totalHs (m : Mol) (i : Nat) : Nat :=
  m.atoms[i]!.frozenHs.getD (m.atoms[i]!.explicitHs + m.implicitHs i)

/-- Cache every atom's explicit valence and implicit H count (RDKit's
`updatePropertyCache` before kekulization), and mark the atoms `adjustHs` may
touch later (`includeAromaticAtoms`, `MolOps.cpp:419`). Aromaticity reads the
cached values. -/
def cacheValences (m : Mol) : Mol :=
  { m with atoms := (List.range m.numAtoms).toArray.map fun i =>
      { m.atoms[i]! with cachedValence := some (m.explicitValence i),
                         cachedImplicit := m.implicitHs i,
                         adjustHs := m.isAromaticAtom i } }

/-- RDKit's final H counts (`adjustHs`, `MolOps.cpp:380-415`, then the last
`updatePropertyCache`): implicit Hs are recomputed on the final graph, and an
atom that is or was aromatic and would *lose* implicit Hs gets them back as
explicit Hs (pyrrole's N–H). The atoms considered are those aromatic before
kekulization plus those aromatic after perception (`MolOps.cpp:639, 673`).
Replaces the counts frozen at the start. -/
def finalizeHs (m : Mol) : Mol := Id.run do
  let mut m := m
  for i in [0:m.numAtoms] do
    let a := m.atoms[i]!
    if a.adjustHs || m.isAromaticAtom i then
      let new := m.implicitHs i
      if new < a.cachedImplicit then
        m := m.modifyAtom i ({ · with explicitHs := a.explicitHs + (a.cachedImplicit - new) })
  let totals := (List.range m.numAtoms).map fun i => m.atoms[i]!.explicitHs + m.implicitHs i
  return { m with atoms := (List.range m.numAtoms).toArray.map fun i =>
      { m.atoms[i]! with frozenHs := some totals[i]! } }

/-- Fix every atom's current total H count, so later bond changes (kekulization,
aromaticity) do not change it. RDKit does the same. -/
def freezeHs (m : Mol) : Mol :=
  { m with atoms := (List.range m.numAtoms).toArray.map fun i =>
      { m.atoms[i]! with frozenHs := some (m.totalHs i) } }

end Mol
end Chem

/-!
# Ring membership

A bond is in a ring exactly when its two atoms stay connected after the bond is
removed, i.e. when it is not a bridge. This is the definition Mathlib uses
(`SimpleGraph.IsBridge`, with `isBridge_iff_adj_and_forall_cycle_notMem` relating
it to cycles), so it is the one we can later prove correct.

Molecules are small, so the simple O(bonds × (atoms + bonds)) check is fine.
-/

namespace Chem
namespace Mol

/-- Atoms reachable from `start` without using bond `skip`. Each round adds all
neighbours of the current set; `numAtoms` rounds always suffice. -/
def reachableWithout (m : Mol) (skip start : Nat) : Array Bool := Id.run do
  let mut seen := (Array.replicate m.numAtoms false).set! start true
  for _ in [0:m.numAtoms] do
    for k in [0:m.numBonds] do
      if k != skip then
        let b := m.bonds[k]!
        if seen[b.src]! && !seen[b.dst]! then seen := seen.set! b.dst true
        else if seen[b.dst]! && !seen[b.src]! then seen := seen.set! b.src true
  return seen

/-- Bond `k` lies on a cycle. -/
def bondInRing (m : Mol) (k : Nat) : Bool :=
  let b := m.bonds[k]!
  (m.reachableWithout k b.src)[b.dst]!

/-- Atom `i` lies on a cycle, i.e. touches a ring bond. -/
def atomInRing (m : Mol) (i : Nat) : Bool :=
  (m.bondsOf i).any m.bondInRing

end Mol
end Chem

/-!
# Cleanup

RDKit's `MolOps::cleanUp` (`MolOps.cpp:51-329`, Release_2026_09_1): rewrites a few
"hypervalent" ways of writing groups into their charge-separated forms. Ported
from `docs/reference/aromaticity_ref.py` (`clean_up`).

* nitro and N-oxide: neutral 5-valent N with `=O`  →  `[N+]-[O-]`
  (`CN(=O)=O` → `C[N+](=O)[O-]`, `n1=O` → `[n+]1[O-]`)
* azide-like: such an N with `#N`  →  `[N+]=[N-]`
* P with `=O` and `=C`/`=N`  →  `[P+]-[O-]`
* Cl/Br/I bonded only to O, valence 3/5/7: each `=O` → `-[O-]` (perchlorate)
-/

namespace Chem
namespace Mol

/-- `MolOps.cpp:51-136`. -/
def nitrogensCleanup (m : Mol) : Mol := Id.run do
  let mut m := m
  let mut consider : List Nat := []
  for i in [0:m.numAtoms] do
    let a := m.atoms[i]!
    if a.atomicNum != 7 || a.charge != 0 || m.explicitValence i != 5 then continue
    consider := consider ++ [i]
    -- the first neutral O on a double bond becomes -O⁻
    let firstO := (m.neighbors i).find? fun (k, j) =>
      m.atoms[j]!.atomicNum == 8 && m.atoms[j]!.charge == 0 && m.bonds[k]!.order == .double
    if let some (k, j) := firstO then
      m := ((m.setOrder k .single).modifyAtom i ({ · with charge := 1 })).modifyAtom j
        ({ · with charge := -1 })
  for i in consider do
    let firstN := (m.neighbors i).find? fun (k, j) =>
      m.atoms[j]!.atomicNum == 7 && m.atoms[j]!.charge == 0 && m.bonds[k]!.order == .triple
    if let some (k, j) := firstN then
      m := ((m.setOrder k .double).modifyAtom i ({ · with charge := 1 })).modifyAtom j
        ({ · with charge := -1 })
  return m

/-- `MolOps.cpp:138-180`: neutral 5-valent P with three neighbours, `=O` and
`=C`/`=N` (the C/N having ≥ 2 neighbours). The last such `=O` becomes `-O⁻`. -/
def phosphorusCleanup (m : Mol) (i : Nat) : Mol := Id.run do
  let a := m.atoms[i]!
  if a.charge != 0 || m.explicitValence i != 5 || m.degree i != 3 then return m
  let mut dblO : Option (Nat × Nat) := none
  let mut dblCN := false
  for (k, j) in m.neighbors i do
    let b := m.atoms[j]!
    if b.atomicNum == 8 && b.charge == 0 && m.bonds[k]!.order == .double then
      dblO := some (k, j)
    else if (b.atomicNum == 6 || b.atomicNum == 7) && m.degree j ≥ 2 &&
        m.bonds[k]!.order == .double then
      dblCN := true
  match dblO with
  | some (k, j) =>
    if dblCN then
      return ((m.setOrder k .single).modifyAtom j ({ · with charge := -1 })).modifyAtom i
        ({ · with charge := 1 })
    else return m
  | none => return m

/-- `MolOps.cpp:182-215`: neutral Cl/Br/I with valence 3, 5 or 7 bonded only to
O. Every `=O` becomes `-O⁻`; the halogen's charge is the number changed. -/
def halogenCleanup (m : Mol) (i : Nat) : Mol := Id.run do
  let a := m.atoms[i]!
  if a.charge != 0 || ![3, 5, 7].contains (m.explicitValence i) then return m
  let nbrs := m.neighbors i
  if !nbrs.all (fun (_, j) => m.atoms[j]!.atomicNum == 8) then return m
  let mut m := m
  let mut fc : Int := 0
  for (k, j) in nbrs do
    if m.bonds[k]!.order == .double then
      m := (m.setOrder k .single).modifyAtom j ({ · with charge := -1 })
      fc := fc + 1
  return m.modifyAtom i ({ · with charge := fc })

/-- `MolOps::cleanUp` (`MolOps.cpp:315-329`). -/
def cleanUp (m : Mol) : Mol := Id.run do
  let mut m := m.nitrogensCleanup
  for i in [0:m.numAtoms] do
    let z := m.atoms[i]!.atomicNum
    if z == 15 then m := m.phosphorusCleanup i
    else if z == 17 || z == 35 || z == 53 then m := m.halogenCleanup i
  return m

end Mol
end Chem

/-!
# Ring set: relevant cycles

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

Ring membership (section "Ring membership" above) does not need this: it only asks *whether*
a bond is on some cycle.
-/

namespace Chem

/-- Number of set bits. -/
def popcount (n : Nat) : Nat := (List.range (n.log2 + 1)).countP n.testBit

/-- Lexicographic order on lists of atom indices. -/
def listLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && listLt as bs)

namespace Mol

/-- Breadth-first distances from `r` (`none` = unreachable) and the visiting order. -/
def bfs (m : Mol) (r : Nat) : Array (Option Nat) × Array Nat := Id.run do
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
def allShortestPaths (m : Mol) (dist : Array (Option Nat)) (order : Array Nat) (r : Nat) :
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
def cycleMask (m : Mol) (cyc : List Nat) : Nat :=
  let n := cyc.length
  (List.range n).foldl (init := 0) fun acc t =>
    match m.bondBetween? (cyc[t]!) (cyc[(t + 1) % n]!) with
    | some k => acc ||| (1 <<< k)
    | none => acc

/-- Candidate cycles (bond mask, atoms), first representative of each bond set kept. -/
def candidateCycles (m : Mol) : Array (Nat × List Nat) := Id.run do
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
def relevantCycles (m : Mol) : Array (List Nat) := Id.run do
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
def ringBonds (m : Mol) (ring : List Nat) : List Nat :=
  let n := ring.length
  (List.range n).filterMap fun t => m.bondBetween? (ring[t]!) (ring[(t + 1) % n]!)

end Mol
end Chem

/-!
# Kekulization

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

namespace Chem
namespace Mol

/-- Does aromatic atom `i` need a double bond? `ev0` is its explicit valence before
kekulization; `wasAromatic k` says whether bond `k` was written aromatic (RDKit
keeps that flag during the whole kekulization). Per-atom part of `markDbondCands`. -/
def needsDoubleBond (m : Mol) (wasAromatic : Nat → Bool) (ev0 : Nat) (i : Nat) : Bool := Id.run do
  let a := m.atoms[i]!
  let z := a.atomicNum
  let totH := a.explicitHs + a.cachedImplicit
  let impl : Int := a.cachedImplicit
  -- aromatic bonds count 1 each, others their (rounded) order
  let mut sbo : Int := totH
  for k in m.bondsOf i do
    let o := m.bonds[k]!.order
    sbo := sbo + (if wasAromatic k then 1 else ((o.halfValence + 1) / 2 : Nat))
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
def kekulizeWorker (m : Mol) (wasAromatic : Nat → Bool) (atoms : List Nat)
    (cands : Array Bool) (done : List Nat) : Option Mol := Id.run do
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
      let nbrs := ((m.neighbors curr).map (·.2)).filter (fun j => atoms.contains j && !done.contains j)
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
      m := m.setOrder k .double
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
              m := m.setOrder k .single
              cands := (cands.set! b.src true).set! b.dst true
        done := keep
      | none => return none
  return some m

/-- Kekulize; fails (like RDKit's "Can't kekulize mol") if no valid structure exists. -/
def kekulize (m : Mol) (rings : Array (List Nat)) : Except String Mol := do
  let aromaticBonds := (List.range m.numBonds).filter (m.bonds[·]!.order == .aromatic)
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
      if out.atoms[i]!.aromatic && out.needsDoubleBond wasAromatic ev0[i]! i then c.set! i true else c
    let done := atoms.filter (!out.atoms[·]!.aromatic)
    for i in atoms do
      if out.atoms[i]!.aromatic then
        for k in out.bondsOf i do
          if wasAromatic k then out := out.setOrder k .single
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
      if [7, 15].contains a.atomicNum && a.charge == 0 && a.explicitHs == 1 then
        let ev := ((out.bondsOf i).foldl (fun s k => s + out.bonds[k]!.order.halfValence) 0) / 2
        out := out.modifyAtom i fun a =>
          { a with aromatic := false, noImplicit := false, explicitHs := 0, cachedValence := some ev }
        out := out.modifyAtom i ({ · with cachedImplicit := out.implicitHs i })
      else
        out := out.modifyAtom i ({ · with aromatic := false })
  if out.bonds.any (·.order == .aromatic) then throw "aromatic bond left after kekulization"
  return out

end Mol
end Chem

/-!
# Aromaticity (RDKit's default model)

Decides which rings are aromatic on a Kekulé structure and marks their bonds
`aromatic` (`Aromaticity.cpp`, `aromaticityHelper`, Release_2026_09_1). Ported
from `docs/reference/aromaticity_ref.py` (`assign_radicals`, `set_aromaticity`).

1. **Electrons per atom.** Each ring atom gets a donor type: how many π electrons
   it can put into the ring (benzene C: 1, pyrrole NH / furan O: 2, ring C=O: 0).
2. **Candidate rings.** A ring is a candidate if every atom can be aromatic.
3. **Hückel 4n + 2**, first on single rings, then on fused groups. Rings are
   "fused" here only if they share exactly one bond and both have ≤ 24 bonds;
   groups of up to 6 rings are tried (`applyHuckelToFused`, `Aromaticity.cpp:334`).
   When a group passes, every bond that occurs once in the group becomes aromatic.
-/

namespace Chem

inductive Donor where
  | vacant | one | two | oneOrTwo | any | none
  deriving BEq, Repr, Inhabited

/-- Fewest and most π electrons of each donor type (`getMinMaxAtomElecs`). -/
def Donor.range : Donor → Nat × Nat
  | .any | .oneOrTwo => (1, 2) | .one => (1, 1) | .two => (2, 2) | .none | .vacant => (0, 0)

namespace Mol

/-- Explicit valence on the Kekulé graph: integer bond orders plus bracket Hs. -/
def kekuleValence (m : Mol) (i : Nat) : Nat :=
  ((m.bondsOf i).foldl (fun s k => s + m.bonds[k]!.order.halfValence) 0) / 2 +
    m.atoms[i]!.explicitHs

/-- The explicit valence RDKit's aromaticity code sees (`Atom::getValence`): the
value cached before kekulization, not one recomputed on the Kekulé graph. They
differ for e.g. arynes (`Clc1ccccc#1`: cached 4, Kekulé 5). -/
def cachedValence (m : Mol) (i : Nat) : Nat :=
  m.atoms[i]!.cachedValence.getD (m.kekuleValence i)

/-- Total H count as RDKit's aromaticity code sees it (`getTotalNumHs`): explicit
Hs plus the cached implicit count. Differs from the parsed count only for odd
atoms like `[nH]=C`, whose implicit H is recomputed during kekulization. -/
def cachedTotalHs (m : Mol) (i : Nat) : Nat :=
  m.atoms[i]!.explicitHs + m.atoms[i]!.cachedImplicit

def isMultiple (o : BondOrder) : Bool := o == .double || o == .triple

/-- `MolOps::assignRadicals` (`MolOps.cpp:437`), for bracket atoms. -/
def assignRadicals (m : Mol) : Mol := Id.run do
  let mut m := m
  for i in [0:m.numAtoms] do
    let a := m.atoms[i]!
    if !a.noImplicit || a.atomicNum == 0 then continue
    let z := a.atomicNum
    let no : Int := outerElectrons z
    let tv : Int := m.kekuleValence i
    let base : Int := if z == 1 || z == 2 then 2 else 8
    let mut nr : Int := base - no - tv + a.charge
    if nr < 0 then
      nr := 0
      if (valences z).length > 1 then
        if let some v := ((valences z).map Int.ofNat).find? (fun v => v - tv + a.charge ≥ 0) then
          nr := v - tv + a.charge
    let nr2 := no - tv - a.charge
    if nr2 ≥ 0 then nr := min nr nr2
    m := m.modifyAtom i ({ · with radicals := nr.toNat })
  return m

/-- π electrons atom `i` could donate, or -1 (`countAtomElec`, `Aromaticity.cpp:656`). -/
def countAtomElec (m : Mol) (i : Nat) : Int := Id.run do
  let a := m.atoms[i]!
  let dv : Int := defaultValence a.atomicNum
  if dv ≤ 1 then return -1
  let deg : Int := m.degree i + m.cachedTotalHs i
  if deg > 3 then return -1
  let nlp := max ((outerElectrons a.atomicNum : Int) - dv - a.charge) 0
  let res := dv - deg + nlp - a.radicals
  if res > 1 && (m.cachedValence i : Int) - m.degree i > 1 then return 1
  return res

/-- Atom across the first non-ring double/triple bond of atom `i`. -/
def exocyclicMultiple? (m : Mol) (ringBonds : List Nat) (i : Nat) : Option Nat :=
  ((m.neighbors i).find? fun (k, _) => !ringBonds.contains k && isMultiple m.bonds[k]!.order).map
    (·.2)

/-- Donor type of atom `i` (`getAtomDonorTypeArom`, `Aromaticity.cpp:581`). -/
def donorType (m : Mol) (ringBonds : List Nat) (i : Nat) : Donor := Id.run do
  let a := m.atoms[i]!
  let mut nelec := m.countAtomElec i
  let who := m.exocyclicMultiple? ringBonds i
  let pullsElectrons := match who with
    | some j => moreElectronegative m.atoms[j]!.atomicNum a.atomicNum
    | none => false
  if nelec < 0 then return .none
  if nelec == 0 then
    if who.isSome then return .vacant
    if (m.bondsOf i).any fun k => ringBonds.contains k && isMultiple m.bonds[k]!.order then
      return .one
    return .none
  if nelec == 1 then
    if who.isSome then return if pullsElectrons then .vacant else .one
    -- any multiple bond at all
    if m.cachedValence i != m.degree i + a.explicitHs then return .one
    if a.charge == 1 then return .vacant
    return .none
  if pullsElectrons then nelec := nelec - 1
  return if nelec % 2 == 1 then .one else .two

/-- Can atom `i` be in an aromatic ring? (`isAtomCandForArom`, `Aromaticity.cpp:440`) -/
def isAromaticCandidate (m : Mol) (i : Nat) (d : Donor) : Bool := Id.run do
  let a := m.atoms[i]!
  let z := a.atomicNum
  if z > 18 && z != 34 && z != 52 then return false
  if d == .none then return false
  let impl := a.cachedImplicit
  let ev := m.cachedValence i
  if defaultValence z > 0 &&
      ev + impl > defaultValence (((z : Int) - a.charge).toNat) then return false
  if a.radicals > 0 && (z != 6 || a.charge != 0) then return false
  if ev > m.degree i + 1 then
    let nMult := ((m.bondsOf i).filter fun k => isMultiple m.bonds[k]!.order).length
    if nMult > 1 then return false
  return true

/-- Hückel's rule over a set of atoms (`applyHuckel`, `Aromaticity.cpp:278`). -/
def huckel (atoms : List Nat) (donor : Array Donor) : Bool := Id.run do
  if (atoms.filter (donor[·]! == .any)).length > 1 then return false
  let lo := atoms.foldl (fun s a => s + (donor[a]!).range.1) 0
  let hi := atoms.foldl (fun s a => s + (donor[a]!).range.2) 0
  if hi ≥ 6 then
    return (List.range (hi + 1 - lo)).any fun t => (lo + t) % 4 == 2
  return hi == 2

/-- All `k`-element subsets of `[0, n)`, in lexicographic order. -/
def combinations (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (combinations n k).flatMap fun c =>
      let start := match c.getLast? with | some x => x + 1 | none => 0
      (List.range (n - start)).map fun d => c ++ [start + d]

/-- Are the rings `rids` connected to each other through `nbrs`? (`checkFused`) -/
def isConnectedSet (rids : List Nat) (nbrs : Array (List Nat)) : Bool := Id.run do
  let some first := rids.head? | return true
  let mut seen := [first]
  for _ in rids do
    for r in seen do
      for v in nbrs[r]! do
        if rids.contains v && !seen.contains v then seen := seen ++ [v]
  return seen.length == rids.length

/-- Mark the aromatic rings (`setAromaticity`, default model). -/
def setAromaticity (m : Mol) (rings : Array (List Nat)) : Mol := Id.run do
  let ringBondSet := (rings.toList.flatMap m.ringBonds).eraseDups
  -- 1-2. donor types (first time each atom is seen) and candidate rings
  let mut seen := Array.replicate m.numAtoms false
  let mut cand := Array.replicate m.numAtoms false
  let mut donor := Array.replicate m.numAtoms Donor.none
  let mut candRings : Array (List Nat) := #[]
  for ring in rings do
    let mut allCand := true
    for i in ring do
      if seen[i]! then
        if !cand[i]! then allCand := false
        continue
      seen := seen.set! i true
      let mut d := m.donorType ringBondSet i
      -- macrocycle rule (Aromaticity.cpp:871): ether-like O/S in a ring of 9 or more
      if d == .two && ring.length ≥ 9 && [8, 16].contains m.atoms[i]!.atomicNum &&
          m.degree i == 2 && m.atoms[i]!.charge == 0 &&
          !(m.bondsOf i).any (isMultiple m.bonds[·]!.order) then
        d := .none
      donor := donor.set! i d
      cand := cand.set! i (m.isAromaticCandidate i d)
      if !cand[i]! then allCand := false
    if allCand then candRings := candRings.push ring
  -- 3. fused systems: rings sharing exactly one bond, each at most 24 bonds
  let nr := candRings.size
  let rbonds := candRings.map m.ringBonds
  let mut nbrs : Array (List Nat) := Array.replicate nr []
  for i in [0:nr] do
    for j in [i + 1:nr] do
      if rbonds[i]!.length ≤ 24 && rbonds[j]!.length ≤ 24 &&
          (rbonds[i]!.filter rbonds[j]!.contains).length == 1 then
        nbrs := (nbrs.modify i (· ++ [j])).modify j (· ++ [i])
  let mut out := m
  for fused in components nr nbrs do
    let nRings := fused.length
    let systemBonds := (fused.flatMap (rbonds[·]!)).eraseDups
    let mut doneBonds : List Nat := []
    for size in [1:(min nRings 6) + 1] do
      if size == 3 && nRings > 300 then break
      if doneBonds.length ≥ systemBonds.length then break
      for comb in combinations nRings size do
        let cur := comb.map (fused[·]!)
        if !isConnectedSet cur nbrs then continue
        -- atoms in 1 or 2 of the chosen rings (GitHub #2895)
        let counts := cur.foldl (fun acc r => candRings[r]!.foldl
          (fun acc a => acc.modify a (· + 1)) acc) (Array.replicate m.numAtoms 0)
        let atoms := (List.range m.numAtoms).filter fun a => counts[a]! == 1 || counts[a]! == 2
        if huckel atoms donor then
          -- bonds that occur once in the group become aromatic
          let all := cur.flatMap (rbonds[·]!)
          for b in all.eraseDups.mergeSort (· ≤ ·) do
            if all.count b == 1 then
              let bd := out.bonds[b]!
              if bd.order == .single || bd.order == .double then
                out := ((out.setOrder b .aromatic).modifyAtom bd.src ({ · with aromatic := true }))
                  |>.modifyAtom bd.dst ({ · with aromatic := true })
              if !doneBonds.contains b then doneBonds := doneBonds ++ [b]
  return out

end Mol
end Chem

/-!
# Sanitization

The Lean counterpart of RDKit's `sanitizeMol` (`MolOps.cpp:604-716`), for the
parts that change bond types, aromatic flags, charges and H counts:

1. **freeze H counts** computed on the graph as written (section "Implicit hydrogens")
2. **cleanUp**: nitro / N-oxide / P / halogen rewrites (section "Cleanup"),
   then RDKit's **strict valence check**: reject atoms with more bonds than any
   allowed valence (section "Implicit hydrogens")
3. **ring set**: relevant cycles (section "Ring set")
4. **kekulize** lowercase-aromatic input (section "Kekulization")
5. **radicals** on bracket atoms, then **aromaticity** (section "Aromaticity")
6. **final H counts** (`adjustHs`) and the **strict valence check again** on
   the final graph, as RDKit does

Reference: `docs/reference/aromaticity_ref.py`, verified against RDKit 2026.09.1.
-/

namespace Chem

def Mol.sanitize (m : Mol) : Except String Mol := do
  let m := m.freezeHs.cleanUp
  -- RDKit's updatePropertyCache(strict=true) after cleanUp (MolOps.cpp:627):
  -- checks valences and caches them for aromaticity
  m.checkValences
  let m := m.cacheValences
  let rings := m.relevantCycles
  let m ← m.kekulize rings
  let m := m.assignRadicals.setAromaticity rings
  -- final H counts (adjustHs), then RDKit checks valences once more at the very
  -- end (MolOps.cpp:700-714): e.g. `C=oC` passes the first check but fails here
  let m := m.finalizeHs
  m.checkValences
  return m

/-- Parse a SMILES string and sanitize it the way RDKit's `MolFromSmiles` does:
the graph that fingerprints and canonicalization start from. -/
def molFromSmiles (s : String) : Except String Mol :=
  Smiles.parse s >>= Mol.sanitize

end Chem
