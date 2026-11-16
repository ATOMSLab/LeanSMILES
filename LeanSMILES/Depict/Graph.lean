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

* **tetrahedral centres** — `Molecule.stereo` holds each centre's
  configuration independently of any listing; `tetra` reads it off as the
  mark for one fixed listing, the neighbors in increasing index order with the
  implicit hydrogen or lone pair last (`sortedLigands`).
* **cis/trans** — a stereo double bond's arrangement (`Molecule.stereo` at
  its ends) is read off as `Edge.sides`: every pair of heavy substituents,
  one at each end, with whether they are cis.

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
  /-- For a double bond with a cis/trans arrangement: every pair of heavy
  substituents `(at src, at dst)` with whether they are cis; `[]` otherwise. -/
  sides : List (ℕ × ℕ × Bool) := []
  deriving Repr, Inhabited

/-- A molecule flattened for layout: atoms, bonds and adjacency lists with `ℕ` indices, built
by `ofMolecule` and read by `Depict.layout` and the SVG / mol-block writers. -/
structure Graph where
  /-- The atoms, in SMILES order. -/
  atoms : Array Atom
  /-- The bonds, in the order the parser created them. -/
  edges : Array Edge
  /-- Neighbors of every atom as `(bond index, neighbor)`, in bond-list order. -/
  adj : Array (List (ℕ × ℕ))
  /-- For each tetrahedral centre, `true` if it is `@` with its ligands listed
  as `sortedLigands` (neighbors in increasing index order, the implicit
  hydrogen or lone pair last), `false` if `@@`. -/
  tetra : Array (Option Bool)
  deriving Repr, Inhabited

/-- Whether a non-ring double bond has a specified cis/trans arrangement. -/
def Edge.stereoSpecified (e : Edge) : Bool := e.kind == .double && !e.ring && !e.sides.isEmpty

namespace Graph

/-- Forget the size index of a `Molecule n`, recording which bonds lie on rings
(`Molecule.bondInRing`) and building the adjacency lists in bond-list order. -/
def ofMolecule {n : ℕ} (m : Molecule n) : Graph :=
  let sides (b : Bond n) : List (ℕ × ℕ × Bool) :=
    match b.kind, m.stereo[b.src] with
    | .double, some (.planar p) =>
      let subs (x y : Fin n) := (m.neighbors x).filter (· != y)
      (subs b.src b.dst).flatMap fun a ↦ (subs b.dst b.src).map fun c ↦
        (a.val, c.val, p.cis (some a) (some c))
    | _, _ => []
  let edges : Array Edge := m.bonds.toArray.map fun b ↦
    ⟨b.src.val, b.dst.val, b.kind, b.dir, m.bondInRing b, sides b⟩
  let adj := Id.run do
    let mut adj : Array (List (ℕ × ℕ)) := Array.replicate n []
    for h : k in [0:edges.size] do
      let e := edges[k]
      adj := adj.modify e.src (· ++ [(k, e.dst)])
      adj := adj.modify e.dst (· ++ [(k, e.src)])
    return adj
  let tetra := Array.ofFn fun i : Fin n ↦ do
    let .tetra t ← m.stereo[i] | none
    let sorted := ((m.neighbors i).mergeSort fun a b ↦ decide (a ≤ b)).map some
    let o ← Ligands.ofList? (if sorted.length = 3 then sorted ++ [none] else sorted)
    if t.isAnticlockwise o then some true
    else if t.isAnticlockwise (o ∘ Ligands.swapLast) then some false
    else none
  ⟨m.atoms.toArray, edges, adj, tetra⟩

/-- The depiction graph of a parsed molecule. -/
def ofMol (M : Mol) : Graph := ofMolecule M.mol

variable (g : Graph)

/-- Number of atoms. -/
def numAtoms : ℕ := g.atoms.size

/-- The atom with index `i` (a default atom if out of range). -/
def atom (i : ℕ) : Atom := g.atoms.getD i default

/-- The degree of atom `i` in the depiction graph: bonds to atoms the string lists, so
implicit hydrogens are not counted but explicit `[H]` atoms are. -/
def degree (i : ℕ) : ℕ := (g.adj.getD i []).length

/-- The index of the bond joining `i` and `j`, if any. -/
def edgeIndex? (i j : ℕ) : Option ℕ :=
  ((g.adj.getD i []).find? (·.2 == j)).map (·.1)

/-- Whether the bond joining `i` and `j` lies on a ring (`false` if there is none). -/
def inRing (i j : ℕ) : Bool :=
  match g.edgeIndex? i j with
  | some k => (g.edges.getD k default).ring
  | none => false

/-- The kind of the bond joining `i` and `j` (single if there is none). -/
def kindBetween (i j : ℕ) : BondKind :=
  match g.edgeIndex? i j with
  | some k => (g.edges.getD k default).kind
  | none => .single

/-- Connected components, each a list of atoms in increasing order, in order of their smallest
atom; `Depict.layout` places them side by side. -/
def components : List (List ℕ) := Id.run do
  let n := g.numAtoms
  let mut assigned := Array.replicate n false
  let mut comps : List (List ℕ) := []
  for i in [0:n] do
    if !assigned[i]! then
      let mut seen := (Array.replicate n false).set! i true
      let mut stack := [i]
      let mut fuel := n + 1
      while 0 < fuel do
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

/-- Atoms reachable from `start` without crossing the bond `u–v`, as a mask over all atoms:
for a non-ring bond and `start = v` this is the `v` side, which the layout reflects to fix a
cis/trans drawing. -/
def sideOf (u v start : ℕ) : Array Bool := Id.run do
  let mut seen := Array.replicate g.numAtoms false
  let mut stack := [start]
  seen := seen.set! start true
  let mut fuel := g.numAtoms + 1
  while 0 < fuel do
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

/-- The listing `tetra` is relative to: the neighbors of `i` in increasing
index order, then `none` for an implicit hydrogen or lone pair when there are
three. -/
def sortedLigands (i : ℕ) : List (Option ℕ) :=
  let sorted := (((g.adj.getD i []).map (·.2)).mergeSort fun a b ↦ decide (a ≤ b)).map some
  if sorted.length == 3 then sorted ++ [none] else sorted

/-- The mark of a tetrahedral centre for `sortedLigands`: `true` for `@`. -/
def tetraMark (i : ℕ) : Option Bool := g.tetra.getD i none

/-- Substituent pairs across non-ring double bonds whose arrangement the
molecule specifies: `(cis pairs, all specified pairs)`. -/
def cisPairs : List (ℕ × ℕ) × List (ℕ × ℕ) := Id.run do
  let mut cis : List (ℕ × ℕ) := []
  let mut all : List (ℕ × ℕ) := []
  for e in g.edges do
    if e.kind != .double || e.ring then continue
    for (a, c, isCis) in e.sides do
      all := (a, c) :: all
      if isCis then cis := (a, c) :: cis
  return (cis, all)

end Graph

end LeanSMILES.Depict
