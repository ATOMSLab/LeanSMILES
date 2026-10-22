/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ejike Ugwuanyi
-/
module

public import LeanSMILES.Fingerprint.Morgan

/-!
# LeanSMILES.Depict.Graph

The view of a `Molecule n` that a 2D depiction needs, with `ℕ` atom indices so
that the numerical layout code (`LeanSMILES.Depict.Layout`) works on plain
arrays: adjacency lists, which bonds lie on rings, all-pairs graph distances,
connected components, and the two pieces of *recorded* stereochemistry read
back into geometric form:

* **tetrahedral centres** — `Atom.chirality` is `@`/`@@` relative to the order
  in which the atom's neighbors appear in the SMILES string. `Molecule` keeps
  the bonds in the order the parser created them, which is not quite that
  order: a ring-closure bond is created when the ring *closes*, at the second
  digit, while the SMILES convention places it at the *first* digit, right
  after the opening atom. `stereoNeighbors` reconstructs the SMILES order from
  the bond list: the atom the centre was reached from, then the implicit
  hydrogen of `[C@H]`, then the ring-closure neighbors, then the branches and
  the chain, each group in bond-list order.
* **cis/trans** — `Bond.dir` is `/` or `\` relative to `src → dst`.
  `dirSides` turns the marks at the two ends of a non-ring double bond into
  "which side" flags: two substituents with equal flags are cis.

Nothing here is chemistry beyond those two conventions; the rest is graph.
-/

@[expose] public section

namespace LeanSMILES.Depict

/-- A bond of the depiction graph: endpoints as `ℕ`, the kind, the `/` `\`
mark relative to `src → dst`, and whether the bond lies on a ring. -/
structure Edge where
  /-- The atom the SMILES string introduced first. -/
  src : ℕ
  /-- The other atom. -/
  dst : ℕ
  /-- The bond kind. -/
  kind : BondKind
  /-- The `/` `\` mark, if written, relative to `src → dst`. -/
  dir : Option BondDir
  /-- Whether the bond lies on a cycle. -/
  ring : Bool
  deriving Repr, Inhabited

/-- A molecule flattened for layout. -/
structure Graph where
  /-- The atoms, in SMILES order. -/
  atoms : Array Atom
  /-- The bonds, in the order the parser created them. -/
  edges : Array Edge
  /-- Neighbors of every atom as `(bond index, neighbor)`, in bond-list order. -/
  adj : Array (List (ℕ × ℕ))
  deriving Repr, Inhabited

namespace Graph

/-- Forget the size index of a `Molecule n`. -/
def ofMolecule {n : ℕ} (m : Molecule n) : Graph :=
  let edges : Array Edge := m.bonds.toArray.map fun b ↦
    ⟨b.src.val, b.dst.val, b.kind, b.dir, m.bondInRing b⟩
  let adj := Id.run do
    let mut adj : Array (List (ℕ × ℕ)) := Array.replicate n []
    for h : k in [0:edges.size] do
      let e := edges[k]
      adj := adj.modify e.src (· ++ [(k, e.dst)])
      adj := adj.modify e.dst (· ++ [(k, e.src)])
    return adj
  ⟨m.atoms.toArray, edges, adj⟩

/-- The depiction graph of a parsed molecule. -/
def ofMol (M : Mol) : Graph := ofMolecule M.mol

variable (g : Graph)

/-- Number of atoms. -/
def numAtoms : ℕ := g.atoms.size

/-- The atom with index `i` (a default atom if out of range). -/
def atom (i : ℕ) : Atom := g.atoms.getD i default

/-- Heavy-atom degree. -/
def degree (i : ℕ) : ℕ := (g.adj.getD i []).length

/-- The index of the bond joining `i` and `j`, if any. -/
def edgeIndex? (i j : ℕ) : Option ℕ :=
  ((g.adj.getD i []).find? (·.2 == j)).map (·.1)

/-- Whether the bond joining `i` and `j` lies on a ring. -/
def inRing (i j : ℕ) : Bool :=
  match g.edgeIndex? i j with
  | some k => (g.edges.getD k default).ring
  | none => false

/-- The kind of the bond joining `i` and `j` (single if there is none). -/
def kindBetween (i j : ℕ) : BondKind :=
  match g.edgeIndex? i j with
  | some k => (g.edges.getD k default).kind
  | none => .single

/-- Connected components, each as a list of atoms in increasing order. -/
def components : List (List ℕ) := Id.run do
  let n := g.numAtoms
  let mut assigned := Array.replicate n false
  let mut comps : List (List ℕ) := []
  for i in [0:n] do
    if !assigned[i]! then
      let mut seen := (Array.replicate n false).set! i true
      let mut stack := [i]
      let mut fuel := n + 1
      while fuel > 0 do
        fuel := fuel - 1
        match stack with
        | [] => break
        | x :: rest =>
          stack := rest
          for (_, y) in g.adj.getD x [] do
            if !seen[y]! then
              seen := seen.set! y true
              stack := y :: stack
      let members := (List.range n).filter fun j ↦ seen[j]!
      for j in members do assigned := assigned.set! j true
      comps := comps ++ [members]
  return comps

/-- The cyclomatic number `bonds − atoms + components`: the number of
independent rings. -/
def ringCount : ℕ := g.edges.size + g.components.length - g.numAtoms

/-- All-pairs shortest path lengths in bonds, by breadth-first search from
every atom (`0` for unreachable pairs). -/
def distances : Array (Array ℕ) := Id.run do
  let n := g.numAtoms
  let mut D : Array (Array ℕ) := #[]
  for s in [0:n] do
    let mut dist := Array.replicate n 0
    let mut seen := (Array.replicate n false).set! s true
    let mut queue := #[s]
    let mut head := 0
    for _ in [0:n + 1] do
      if h : head < queue.size then
        let u := queue[head]
        head := head + 1
        for (_, v) in g.adj.getD u [] do
          if !seen[v]! then
            seen := seen.set! v true
            dist := dist.set! v (dist[u]! + 1)
            queue := queue.push v
      else break
    D := D.push dist
  return D

/-- Atoms reachable from `start` without crossing the bond `u–v`. -/
def sideOf (u v start : ℕ) : Array Bool := Id.run do
  let mut seen := Array.replicate g.numAtoms false
  let mut stack := [start]
  seen := seen.set! start true
  let mut fuel := g.numAtoms + 1
  while fuel > 0 do
    fuel := fuel - 1
    match stack with
    | [] => break
    | x :: rest =>
      stack := rest
      for (_, y) in g.adj.getD x [] do
        if (x == u && y == v) || (x == v && y == u) then continue
        if !seen[y]! then
          seen := seen.set! y true
          stack := y :: stack
  return seen

/-! ### Reading the stereochemistry back -/

/-- The bond that introduced atom `d`: the first bond in the list with `dst = d`
and `src < d`. Every atom but the first of each component has one, and it comes
before any ring-closure bond at `d`, because the closing digit follows the
atom. -/
def chainBond? (d : ℕ) : Option ℕ :=
  ((g.adj.getD d []).find? fun (k, _) ↦
    let e := g.edges.getD k default
    e.dst == d && e.src < d).map (·.1)

/-- The neighbors of a stereocentre in the order the SMILES string lists them,
`none` standing for the implicit hydrogen of `[C@H]`: the atom the centre was
reached from, the hydrogen, the ring-closure neighbors, then the branches and
the chain. A centre with three listed neighbors and no hydrogen (a sulfoxide
sulfur, say) gets its lone pair as a fourth entry at the end. -/
def stereoNeighbors (i : ℕ) : List (Option ℕ) := Id.run do
  let a := g.atom i
  let parent := g.chainBond? i
  let nbrs := g.adj.getD i []
  let mut rings : List (Option ℕ) := []
  let mut children : List (Option ℕ) := []
  for (k, j) in nbrs do
    if parent == some k then continue
    let e := g.edges.getD k default
    if e.src == i && g.chainBond? j == some k then children := children ++ [some j]
    else rings := rings ++ [some j]
  let before := match parent with
    | some k => [some (g.edges.getD k default).src]
    | none => []
  let hydrogen := if a.explicitH == some 1 then [none] else []
  let listed := before ++ hydrogen ++ rings ++ children
  return if listed.length == 3 && hydrogen.isEmpty then listed ++ [none] else listed

/-- The `/` `\` marks at a bond's ends as side flags: at `src` the flag for
`dst`, at `dst` the flag for `src`, chosen so that two substituents of a double
bond with *equal* flags lie on the same side (cis). -/
def dirFlags (e : Edge) : Option (Bool × Bool) :=
  e.dir.map fun d ↦ (d != .up, d == .up)

/-- The side flags of every marked single bond at atom `i`, as
`(neighbor, flag)`. -/
def dirSides (i : ℕ) : List (ℕ × Bool) :=
  (g.adj.getD i []).filterMap fun (k, j) ↦
    let e := g.edges.getD k default
    (dirFlags e).map fun (atSrc, atDst) ↦ (j, if e.src == i then atSrc else atDst)

/-- Substituent pairs across non-ring double bonds whose arrangement the `/` `\`
marks specify: `(cis pairs, all specified pairs)`. -/
def cisPairs : List (ℕ × ℕ) × List (ℕ × ℕ) := Id.run do
  let mut cis : List (ℕ × ℕ) := []
  let mut all : List (ℕ × ℕ) := []
  for e in g.edges do
    if e.kind != .double || e.ring then continue
    let du := (g.dirSides e.src).filter (·.1 != e.dst)
    let dv := (g.dirSides e.dst).filter (·.1 != e.src)
    for (a, sa) in du do
      for (c, sc) in dv do
        all := (a, c) :: all
        if sa == sc then cis := (a, c) :: cis
  return (cis, all)

/-- Whether a non-ring double bond has `/` `\` marks on both ends. -/
def stereoSpecified (e : Edge) : Bool :=
  e.kind == .double && !e.ring &&
    ((g.dirSides e.src).any (·.1 != e.dst)) && ((g.dirSides e.dst).any (·.1 != e.src))

end Graph

end LeanSMILES.Depict
