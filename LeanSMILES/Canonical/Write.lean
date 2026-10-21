import LeanSMILES.Canonical.Sanitize

/-!
# LeanSMILES.Canonical.Write

Molecule graph → canonical SMILES. Entry point: `Chem.canonicalSmiles`.
-/

/-!
# Canonical SMILES

`Chem.canonicalSmiles "…"` gives the same string as RDKit's
`Chem.MolToSmiles(Chem.MolFromSmiles(s), isomericSmiles=False)` (RDKit 2026.09.1):
one fixed spelling per molecule, however the input was written.

Ported from `docs/reference/canon_ref.py` (verified against RDKit on 12,960
molecules). Two parts, each with RDKit file:line references:

1. **Rank the atoms** (`Canon::rankMolAtoms`, `new_canon.h` / `new_canon.cpp`).
   All atoms start in one class. Classes are split by comparing degree, element,
   H count, charge and then the classes of the neighbours, until nothing changes
   (like Morgan's iteration). A "special symmetry" pass helps some symmetric ring
   systems. Remaining ties are broken one atom at a time.
2. **Write the string** (`Canon.cpp`, `SmilesWrite.cpp`). Start at the lowest-
   ranked atom and walk the molecule depth-first: ring closures first, then
   branches, then ring continuation. Ring digits are reused, brackets and bond
   symbols follow RDKit's rules. Separate fragments are sorted and joined by `.`.
-/

namespace Chem

/-! ## Shared helpers -/

/-- Neighbours of atom `i` as (atom, RDKit bond type 1/2/3/12, bond index). -/
def adjOf (m : Mol) (i : Nat) : List (Nat × Nat × Nat) :=
  (m.neighbors i).map fun (k, o) => (o, m.bonds[k]!.order.rdkitType, k)

/-- RDKit compares formal charges as `unsigned int` (`new_canon.h:410-416`), so
the order is 0 < 1 < 2 < … < −2 < −1. -/
def chargeKey (c : Int) : Nat := if c ≥ 0 then c.toNat else (4294967296 + c).toNat

def cmpNat (a b : Nat) : Ordering := compare a b

/-- Lexicographic comparison; a shorter prefix is smaller (`std::vector` `<`). -/
def cmpLex {α} (cmp : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => match cmp a b with
    | .eq => cmpLex cmp as bs
    | o => o

/-- Stable insertion sort by `cmp`. -/
def insertionSort {α} (cmp : α → α → Ordering) (xs : List α) : List α :=
  xs.foldl (fun sorted x =>
    -- insert after every element that is not greater than x (stable)
    let (le, gt) := sorted.span (cmp · x != .gt)
    le ++ x :: gt) []

/-! ## Part 1: ranking -/

/-- Per-molecule data the comparisons read. -/
structure RankInput where
  n : Nat
  z : Array Nat
  charge : Array Int
  hs : Array Nat
  deg : Array Nat
  adj : Array (List (Nat × Nat × Nat))
  inRing : Array Bool
  multiRing : Array Bool

/-- An atom's neighbours as (bond type, neighbour class), largest first
(`bondholder`, `new_canon.h:84-113`). -/
def bondHolders (R : RankInput) (index : Array Nat) (i : Nat) : List (Nat × Nat) :=
  let l := R.adj[i]!.map fun (j, t, _) => (t, index[j]!)
  insertionSort (fun a b => cmpLex cmpNat [b.1, b.2] [a.1, a.2]) l

def cmpBonds (R : RankInput) (index : Array Nat) (i j : Nat) : Ordering :=
  cmpLex (fun a b => cmpLex cmpNat [a.1, a.2] [b.1, b.2])
    (bondHolders R index i) (bondHolders R index j)

/-- `AtomCompareFunctor` as `MolToSmiles(isomericSmiles=False)` uses it
(`new_canon.h:323-518, 547-593`): class, degree, element, H count, charge
(unsigned), then the neighbour lists. -/
def cmpAtom (R : RankInput) (index : Array Nat) (i j : Nat) : Ordering :=
  match cmpLex cmpNat
      [index[i]!, R.deg[i]!, R.z[i]!, R.hs[i]!, chargeKey R.charge[i]!]
      [index[j]!, R.deg[j]!, R.z[j]!, R.hs[j]!, chargeKey R.charge[j]!] with
  | .eq => cmpBonds R index i j
  | o => o

/-- Breadth-first "shell" invariants of each ring atom, for the special symmetry
pass (`compareRingAtomsConcerningNumNeighbors`, `new_canon.cpp:149-272`).
Returns (neighborNum, revisited) per atom; -1 ends each level. -/
def ringShells (R : RankInput) : Array (List Int) × Array (List Int) := Id.run do
  let n := R.n
  let mut nbrNum : Array (List Int) := Array.replicate n []
  let mut revisited : Array (List Int) := Array.replicate n []
  for idx in [0:n] do
    if !R.inRing[idx]! then continue
    let mut visited := Array.replicate n false
    let mut lastLevel := Array.replicate n false
    let mut curLevel := Array.replicate n false
    let mut numL : List Int := []
    let mut revL : List Int := []
    let mut queue : List Nat := [idx]
    while !queue.isEmpty do
      let mut count : Int := 0
      let mut nextLevel : List Nat := []
      for x in queue do
        if !R.inRing[x]! then continue
        lastLevel := lastLevel.set! x true
        visited := visited.set! x true
        for (j, _, _) in R.adj[x]! do
          if !visited[j]! then
            curLevel := curLevel.set! j true
            count := count + 1
            visited := visited.set! j true
            nextLevel := nextLevel ++ [j]
      -- how often each current/last-level atom neighbours the next level
      let mut rev := Array.replicate n 0
      let mut touched : List Nat := []
      for i in nextLevel do
        for (j, _, _) in R.adj[i]! do
          if curLevel[j]! || lastLevel[j]! then
            if rev[j]! == 0 then touched := touched ++ [j]
            rev := rev.modify j (· + 1)
      lastLevel := Array.replicate n false
      for i in nextLevel do
        lastLevel := lastLevel.set! i true
        curLevel := curLevel.set! i false
      revL := revL ++ (insertionSort cmpNat (touched.map (rev[·]!))).map Int.ofNat ++ [-1]
      numL := numL ++ [count, -1]
      queue := nextLevel
    nbrNum := nbrNum.set! idx numL
    revisited := revisited.set! idx revL
  return (nbrNum, revisited)

/-- `SpecialSymmetryAtomCompareFunctor` (`new_canon.h:216-274`). -/
def cmpSpecial (R : RankInput) (shells : Array (List Int) × Array (List Int))
    (index : Array Nat) (i j : Nat) : Ordering :=
  match cmpLex compare shells.1[i]! shells.1[j]! with
  | .eq => match cmpLex compare shells.2[i]! shells.2[j]! with
    | .eq => cmpBonds R index i j
    | o => o
  | o => o

/-- The partition machinery (`new_canon.cpp:96-147`, `new_canon.h:727-887`).
`index[a]` is atom a's class = the position of its partition in `order`;
`count[a]` > 0 marks the first atom of a partition (its size). -/
structure Parts where
  index : Array Nat
  order : Array Nat
  count : Array Nat
  next : Array Int        -- -2: not queued; otherwise the next queued partition
  active : Int            -- head of the queue of partitions to refine (-1: empty)

/-- Queue every partition with more than one atom (`ActivatePartitions`). -/
def Parts.activate (P : Parts) (n : Nat) : Parts := Id.run do
  let mut P := { P with active := -1, next := Array.replicate n (-2) }
  let mut i := 0
  while i < n do
    let j := P.order[i]!
    if P.count[j]! > 1 then
      P := { P with next := P.next.set! j P.active, active := j }
      i := i + P.count[j]!
    else i := i + 1
  return P

/-- Queue the partitions containing any of `atoms`' neighbours. -/
def Parts.touch (P : Parts) (R : RankInput) (atoms : List Nat) : Parts := Id.run do
  let mut touched := Array.replicate R.n false
  for a in atoms do
    for (j, _, _) in R.adj[a]! do
      touched := touched.set! P.index[j]! true
  let mut P := P
  for ii in [0:R.n] do
    if touched[ii]! then
      let p := P.order[ii]!
      if P.count[p]! > 1 && P.next[p]! == -2 then
        P := { P with next := P.next.set! p P.active, active := p }
  return P

/-- Split the queued partitions until nothing changes (`RefinePartitions`). -/
def Parts.refine (P : Parts) (R : RankInput) (cmp : Array Nat → Nat → Nat → Ordering) :
    Parts := Id.run do
  let mut P := P
  let mut symclass := 0
  while P.active != -1 do
    let partition := P.active.toNat
    P := { P with active := P.next[partition]!, next := P.next.set! partition (-2) }
    let len := P.count[partition]!
    let offset := P.index[partition]!
    -- sort the partition's atoms (stable) and mark runs of equal atoms
    let seg := insertionSort (cmp P.index) ((List.range len).map (P.order[offset + ·]!))
    let mut count := P.count
    let mut s := 0
    while s < seg.length do
      let mut e := s + 1
      while e < seg.length && cmp P.index seg[s]! seg[e]! == .eq do e := e + 1
      count := count.set! seg[s]! (e - s)
      for q in [s + 1:e] do count := count.set! seg[q]! 0
      s := e
    let mut order := P.order
    for k in [0:len] do order := order.set! (offset + k) seg[k]!
    P := { P with order, count }
    -- new class numbers for the atoms after the first run
    let first := P.order[offset]!
    let mut index := P.index
    let mut moved : List Nat := []
    for i in [P.count[first]!:len] do
      let idx := P.order[offset + i]!
      if P.count[idx]! > 0 then symclass := offset + i
      index := index.set! idx symclass
      moved := moved ++ [idx]
    P := { P with index }
    P := P.touch R moved
  return P

/-- Promote one atom of each remaining tie and refine again (`BreakTies`). -/
def Parts.breakTies (P : Parts) (R : RankInput) (cmp : Array Nat → Nat → Nat → Ordering) :
    Parts := Id.run do
  let mut P := P
  let mut i := 0
  while i < R.n do
    let partition := P.order[i]!
    let oldPart := P.index[partition]!
    while P.count[partition]! > 1 do
      let len := P.count[partition]!
      let offset := P.index[partition]! + len - 1
      let idx := P.order[offset]!
      P := { P with index := P.index.set! idx offset,
                    count := (P.count.set! partition (len - 1)).set! idx 1 }
      if R.deg[idx]! < 1 then continue
      P := (P.touch R [idx]).refine R cmp
    if P.index[partition]! == oldPart then i := i + 1
  return P

/-- Canonical ranks 0 … n−1, all distinct (`rankMolAtoms` → `rankWithFunctor`,
`new_canon.cpp:274-387`). -/
def rankAtoms (R : RankInput) : Array Nat := Id.run do
  let n := R.n
  if n == 0 then return #[]
  let P0 : Parts := { index := Array.replicate n 0, order := (List.range n).toArray,
                      count := (Array.replicate n 0).set! 0 n,
                      next := Array.replicate n (-2), active := -1 }
  let mut P := (P0.activate n).refine R (cmpAtom R)
  -- special symmetry pass, only for some symmetric ring systems (new_canon.cpp:339-375)
  let mut ties := false
  let mut symRingAtoms := 0
  let mut ringAtoms := 0
  let mut branching := false
  for i in [0:n] do
    let o := P.order[i]!
    if R.inRing[o]! then
      if P.count[o]! > 2 then symRingAtoms := symRingAtoms + P.count[o]!
      ringAtoms := ringAtoms + 1
      if R.multiRing[o]! && P.count[o]! > 1 then branching := true
    if P.count[i]! == 0 then ties := true
  if ties && ringAtoms > 0 && 2 * symRingAtoms > ringAtoms && branching then
    let shells := ringShells R
    P := (P.activate n).refine R (cmpSpecial R shells)
  P := P.breakTies R (cmpAtom R)
  return (List.range n).foldl (fun rank i => rank.set! P.order[i]! P.index[P.order[i]!]!)
    (Array.replicate n 0)

/-! ## Part 2: writing the string -/

/-- Elements in the SMILES organic subset (`SmilesWrite.cpp:32`). -/
def organicZ : List Nat := [5, 6, 7, 8, 9, 15, 16, 17, 35, 53]
/-- Written in lowercase when aromatic (`SmilesWrite.cpp:196-206`). -/
def aromaticLowerZ : List Nat := [5, 6, 7, 8, 14, 15, 16, 33, 34, 52]
/-- Not metals (`QueryOps.cpp:434-470`); anything else counts as a metal. -/
def nonMetalZ : List Nat := [0, 1, 2, 5, 6, 7, 8, 9, 10, 14, 15, 16, 17, 18, 33, 34, 35, 36,
  52, 53, 54, 85, 86]

/-- Total valence of a neutral organic-subset atom (`Atom.cpp:337-415`), for the
"unusual valence needs brackets" rule. -/
def totalValence (m : Mol) (i : Nat) : Nat := Id.run do
  let a := m.atoms[i]!
  let mut acc := 2 * a.explicitHs
  for (_, t, _) in adjOf m i do
    acc := acc + (if t == 12 then 3 else 2 * t)
  let vl := valences a.atomicNum
  let dv := vl.head?.getD 0
  if a.aromatic && acc > 2 * dv then
    let pval := (vl.filter (2 * · ≤ acc)).getLast?.getD dv
    if acc ≤ 2 * pval + 3 then acc := 2 * pval
  return (acc + 1) / 2 + (m.totalHs i - a.explicitHs)

/-- Does atom `i` need `[...]`? (`atomNeedsBracket`, `SmilesWrite.cpp:107-153`) -/
def needsBracket (m : Mol) (i : Nat) : Bool :=
  let a := m.atoms[i]!
  let z := a.atomicNum
  !organicZ.contains z || a.charge != 0 || a.radicals > 0 ||
  ((z == 7 || z == 15) && a.aromatic && a.explicitHs > 0) ||
  (m.totalHs i > 0 && totalValence m i != (valences z).head?.getD 0) ||
  (adjOf m i).any fun (o, _, _) => !nonMetalZ.contains m.atoms[o]!.atomicNum

/-- The atom token, e.g. `C`, `c`, `[nH]`, `[N+]`, `[O-2]` (`SmilesWrite.cpp:157-252`). -/
def atomToken (m : Mol) (i : Nat) : String := Id.run do
  let a := m.atoms[i]!
  let mut sym := symbol a.atomicNum
  if a.aromatic && aromaticLowerZ.contains a.atomicNum then
    sym := String.ofList (match sym.toList with | c :: cs => c.toLower :: cs | [] => [])
  if !needsBracket m i then return sym
  let h := m.totalHs i
  let hs := if h == 0 then "" else if h == 1 then "H" else s!"H{h}"
  let q := a.charge
  let qs := if q == 0 then "" else if q == 1 then "+" else if q > 1 then s!"+{q}"
            else if q == -1 then "-" else s!"{q}"
  return s!"[{sym}{hs}{qs}]"

/-- The bond symbol between atoms `a1` and `a2` (`GetBondSmiles`, `SmilesWrite.cpp:254-364`). -/
def bondToken (m : Mol) (t a1 a2 : Nat) : String :=
  let bothAromatic := m.atoms[a1]!.aromatic && m.atoms[a2]!.aromatic
  match t with
  | 1 => if bothAromatic then "-" else ""
  | 2 => "="
  | 3 => "#"
  | 12 => if bothAromatic then "" else ":"
  | _ => "~"

/-- Order in which a neighbour is visited (`Canon.cpp:890-921, 1075-1086`):
ring closures first, then non-ring branches, then ring bonds (aromatic first). -/
def visitKey (rank : Nat) (t : Nat) (grey ringBond : Bool) : Int :=
  let N : Int := 5000
  if grey then rank - 33 * N * N + (32 - t) * N
  else if ringBond then rank + (32 - t) * N * N
  else rank

inductive Token where
  | atom (a : Nat) | bond (t a o : Nat) | ring (r : Nat) | openBranch | closeBranch

structure WalkState where
  color : Array Nat               -- 0 white, 1 grey, 2 black
  closures : Array (List Nat)     -- ring-closure bonds per atom
  cycleFree : Array Bool          -- ring indices available
  bondRing : Array Nat            -- ring index given to a bond (0: none yet)
  tokens : Array Token

/-- Pass 1: find the ring-closure bonds by a depth-first walk (`dfsFindCycles`). -/
def findCycles (m : Mol) (rank : Array Nat) (inRing : Array Bool) :
    Nat → Nat → Option Nat → StateM WalkState Unit
  | 0, _, _ => pure ()
  | fuel + 1, a, inBond => do
    modify fun s => { s with color := s.color.set! a 1 }
    let s ← get
    let poss := insertionSort (fun x y => compare x.1 y.1)
      ((adjOf m a).filter (some ·.2.2 != inBond) |>.map fun (o, t, k) =>
        (visitKey rank[o]! t (s.color[o]! == 1) inRing[k]!, o, k))
    for (_, o, k) in poss do
      let c := (← get).color[o]!
      if c == 0 then findCycles m rank inRing fuel o (some k)
      else if c == 1 then
        modify fun s => { s with closures := (s.closures.modify o (· ++ [k])).modify a (· ++ [k]) }
    modify fun s => { s with color := s.color.set! a 2 }

/-- Pass 2: emit atoms, bonds, ring digits and branches (`dfsBuildStack`). -/
def buildTokens (m : Mol) (rank : Array Nat) (inRing : Array Bool) :
    Nat → Nat → Option Nat → StateM WalkState Unit
  | 0, _, _ => pure ()
  | fuel + 1, a, inBond => do
    let mut seen : List Nat := [a]
    modify fun s => { s with tokens := s.tokens.push (.atom a), color := s.color.set! a 1 }
    let mut closed : List Nat := []
    for k in (← get).closures[a]! do
      let o := m.bonds[k]!.other a
      seen := o :: seen
      let r := (← get).bondRing[k]!
      if r != 0 then
        -- closing a ring: bond symbol then digit
        modify fun s => { s with tokens := (s.tokens.push (.bond m.bonds[k]!.order.rdkitType a o)).push (.ring r) }
        closed := closed ++ [r - 1]
      else
        -- opening a ring: lowest free index
        let low := ((← get).cycleFree.findIdx? id).getD 0
        modify fun s => { s with cycleFree := s.cycleFree.set! low false,
                                 bondRing := s.bondRing.set! k (low + 1),
                                 tokens := s.tokens.push (.ring (low + 1)) }
    for r in closed do
      modify fun s => { s with cycleFree := s.cycleFree.set! r true }
    let s ← get
    let poss := insertionSort (fun x y => compare x.1 y.1)
      ((adjOf m a).filter (fun (o, _, k) => some k != inBond && s.color[o]! == 0 && !seen.contains o)
        |>.map fun (o, t, k) => (visitKey rank[o]! t false inRing[k]!, o, k))
    for p in [0:poss.length] do
      let (_, o, k) := poss[p]!
      if (← get).color[o]! != 0 then continue
      let last := p + 1 == poss.length
      if !last then modify fun s => { s with tokens := s.tokens.push .openBranch }
      modify fun s => { s with tokens := s.tokens.push (.bond m.bonds[k]!.order.rdkitType a o) }
      buildTokens m rank inRing fuel o (some k)
      if !last then modify fun s => { s with tokens := s.tokens.push .closeBranch }
    modify fun s => { s with color := s.color.set! a 2 }

/-- Turn the tokens into text, renumbering ring digits as the lowest digit not in
use (`SmilesWrite.cpp:409-487`). -/
def render (m : Mol) (tokens : Array Token) : String := Id.run do
  let mut out := ""
  let mut ringMap : List (Nat × Nat) := []   -- ring index ↦ digit written
  let mut toErase : List Nat := []
  for tok in tokens do
    match tok with
    | .atom a =>
      ringMap := ringMap.filter (!toErase.contains ·.1)
      toErase := []
      out := out ++ atomToken m a
    | .bond t a o => out := out ++ bondToken m t a o
    | .ring r =>
      let digit ← match ringMap.lookup r with
        | some d => do toErase := toErase ++ [r]; pure d
        | none => do
          let d := (List.range (ringMap.length + 2)).find? (fun d => d ≥ 1 && !ringMap.any (·.2 == d)) |>.getD 1
          ringMap := ringMap ++ [(r, d)]
          pure d
      out := out ++ (if digit < 10 then toString digit
                     else if digit < 100 then s!"%{digit}" else s!"%({digit})")
    | .openBranch => out := out ++ "("
    | .closeBranch => out := out ++ ")"
  return out

/-- Canonical SMILES of one connected fragment. -/
def fragmentSmiles (m : Mol) : String := Id.run do
  let n := m.numAtoms
  let inRingBond := (List.range m.numBonds).toArray.map m.bondInRing
  let nRingBonds := (List.range n).toArray.map fun i =>
    ((m.bondsOf i).filter (inRingBond[·]!)).length
  let R : RankInput :=
    { n, z := m.atoms.map (·.atomicNum), charge := m.atoms.map (·.charge),
      hs := (List.range n).toArray.map m.totalHs, deg := (List.range n).toArray.map m.degree,
      adj := (List.range n).toArray.map (adjOf m),
      inRing := nRingBonds.map (· > 0),
      -- "in more than one ring": proxy used by the reference (≥ 3 ring bonds)
      multiRing := nRingBonds.map (· ≥ 3) }
  let rank := rankAtoms R
  let start := (List.range n).foldl (fun s i => if rank[i]! < rank[s]! then i else s) 0
  let s0 : WalkState :=
    { color := Array.replicate n 0, closures := Array.replicate n [],
      cycleFree := Array.replicate (m.numBonds + 1) true, bondRing := Array.replicate m.numBonds 0,
      tokens := #[] }
  let s1 := ((findCycles m rank inRingBond (n + 1) start none).run s0).2
  let s2 := ((buildTokens m rank inRingBond (n + 1) start none).run
    { s1 with color := Array.replicate n 0 }).2
  return render m s2.tokens

/-- The connected fragments of `m`, each as its own molecule (atoms in ascending
order, bonds in original order: `SmilesWrite.cpp:507-534`). -/
def fragments (m : Mol) : List Mol := Id.run do
  let n := m.numAtoms
  let mut comp : Array (Option Nat) := Array.replicate n none
  let mut frags : List (List Nat) := []
  for s in [0:n] do
    if comp[s]!.isSome then continue
    let c := frags.length
    comp := comp.set! s (some c)
    let mut members : List Nat := []
    let mut stack := [s]
    while !stack.isEmpty do
      let x := stack.head!
      stack := stack.tail
      members := x :: members
      for (_, y) in m.neighbors x do
        if comp[y]!.isNone then
          comp := comp.set! y (some c)
          stack := y :: stack
    frags := frags ++ [members.mergeSort (· ≤ ·)]
  return frags.map fun fr =>
    let local_ (i : Nat) := fr.idxOf i
    { atoms := (fr.map (m.atoms[·]!)).toArray,
      bonds := m.bonds.filterMap fun b =>
        if fr.contains b.src && fr.contains b.dst
        then some { b with src := local_ b.src, dst := local_ b.dst } else none }

/-- Canonical SMILES of a sanitized molecule. -/
def Mol.canonicalSmiles (m : Mol) : String :=
  ".".intercalate (insertionSort (fun a b => compare a b) ((fragments m).map fragmentSmiles))

/-- SMILES in, RDKit-style canonical SMILES (without stereo marks) out. -/
def canonicalSmiles (s : String) : Except String String :=
  (molFromSmiles s).map (·.canonicalSmiles)

end Chem
