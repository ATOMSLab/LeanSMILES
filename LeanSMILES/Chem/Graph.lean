/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Chem.Molecule
public import LeanSMILES.Chem.BondMatrix
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.NormNum

/-!
# LeanSMILES.Chem.Graph

The mathematical views of a `Molecule n`, and the proofs that they agree:

* `Molecule.graph : SimpleGraph (Fin n)` — Mathlib's simple graph on the atom
  indices, adjacent when some bond joins them.  It has decidable adjacency, so
  all of Mathlib's finite-graph machinery (`degree`, `edgeFinset`, the
  handshake lemma, `adjMatrix`) is available and computable.
* `Molecule.adjMatrix : Matrix (Fin n) (Fin n) ℚ` — the bond-order-weighted
  adjacency matrix, symmetric with zero diagonal; it is nonzero exactly where
  the graph is adjacent, and Mathlib's 0/1 `adjMatrix` is its indicator.
* `Molecule.toBondMatrix : BondMatrix n` and `Molecule.toFlatMatrix : FlatMatrix n`
  — the same two matrices as the subtypes of `LeanSMILES.Chem.BondMatrix`, the
  first backed by a materialized table so that `B i j` is an O(1) lookup.

`ofAdjMatrix` decodes a valid matrix back into a molecule whose matrix, graph
and bond kinds are the originals.  **Nothing is lost**: what a symmetric
matrix cannot hold is the `src → dst` orientation of a bond (the `/` `\`
marks) and the order of the bond list.  `normalize` forgets exactly those,
`IsNormal` says a molecule already has, and `normalEquiv` is the theorem:
normal molecules are *exactly* atoms together with a bond matrix.

Relabeling the atoms by a permutation gives an isomorphic graph
(`relabelIso`) — which is what makes canonicalization (`LeanSMILES.SMILES.Canon`)
a change of *labels* and nothing else.
-/

@[expose] public section

namespace LeanSMILES

variable {n : ℕ}

namespace Molecule

variable (m : Molecule n)

/-! ### The simple graph -/

/-- The molecular graph: atoms are adjacent when some bond joins them. -/
def graph : SimpleGraph (Fin n) where
  Adj i j := s(i, j) ∈ m.edges
  symm := by
    intro i j h
    rwa [Sym2.eq_swap]
  loopless := ⟨fun i h ↦ by
    obtain ⟨b, -, hb⟩ := List.mem_map.mp h
    exact b.edge_ne_diag i hb⟩

instance : DecidableRel m.graph.Adj :=
  fun i j ↦ inferInstanceAs (Decidable (s(i, j) ∈ m.edges))

/-- Adjacency in the molecular graph, unfolded: some bond has the edge `s(i, j)`. -/
lemma adj_iff (i j : Fin n) : m.graph.Adj i j ↔ ∃ b ∈ m.bonds, b.edge = s(i, j) :=
  List.mem_map

/-- Mathlib's edge set is exactly the bond list. -/
lemma edgeFinset_eq : m.graph.edgeFinset = m.edges.toFinset :=
  Finset.ext fun e ↦ Sym2.ind (fun i j ↦ by simp [graph]) e

/-- Because no two bonds join the same atoms, Mathlib counts the bonds. -/
theorem card_edgeFinset : m.graph.edgeFinset.card = m.numBonds := by
  rw [edgeFinset_eq, edges, List.toFinset_card_of_nodup m.nodup, List.length_map, numBonds]

/-- The handshake lemma, for molecules: degrees sum to twice the bond count. -/
theorem sum_degrees : ∑ i, m.graph.degree i = 2 * m.numBonds :=
  m.card_edgeFinset ▸ m.graph.sum_degrees_eq_twice_card_edges

/-! ### The adjacency matrix -/

/-- `bondBetween` is symmetric: the edge `s(i, j)` is the edge `s(j, i)`. -/
lemma bondBetween_symm (i j : Fin n) : m.bondBetween i j = m.bondBetween j i := by
  simp only [bondBetween, @Sym2.eq_swap _ i j]

/-- No bond joins an atom to itself. -/
lemma bondBetween_self (i : Fin n) : m.bondBetween i i = none := by
  simp [bondBetween, List.find?_eq_none, Bond.edge_ne_diag]

/-- Adjacency is exactly `bondBetween` finding a bond: the `Prop` form of `Molecule.adjacent`. -/
lemma adj_iff_isSome (i j : Fin n) : m.graph.Adj i j ↔ (m.bondBetween i j).isSome := by
  simp [adj_iff, bondBetween]

/-- The bond-order-weighted adjacency matrix, over `ℚ`. -/
def adjMatrix : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j ↦ ((m.bondBetween i j).map (·.kind.order)).getD 0

/-- An entry of the weighted matrix: the order of the bond between `i` and `j`, or `0`. -/
lemma adjMatrix_apply (i j : Fin n) :
    m.adjMatrix i j = ((m.bondBetween i j).map (·.kind.order)).getD 0 := rfl

/-- The weighted adjacency matrix is symmetric: a bond has no direction. -/
lemma isSymm_adjMatrix : m.adjMatrix.IsSymm :=
  Matrix.IsSymm.ext fun i j ↦ by rw [adjMatrix_apply, adjMatrix_apply, bondBetween_symm]

/-- The weighted matrix has zero diagonal: no atom is bonded to itself. -/
@[simp] lemma adjMatrix_apply_self (i : Fin n) : m.adjMatrix i i = 0 := by
  simp [adjMatrix_apply, bondBetween_self]

/-- Reading a bond kind off the weighted matrix entry gives the kind of the bond there, if any:
the way to pass between the matrix and `bondBetween` without unfolding either. -/
lemma ofOrder?_adjMatrix (i j : Fin n) :
    BondKind.ofOrder? (m.adjMatrix i j) = (m.bondBetween i j).map (·.kind) := by
  rw [adjMatrix_apply]
  rcases m.bondBetween i j with _ | b
  · norm_num [BondKind.ofOrder?]
  · simp

/-- The weighted matrix is nonzero exactly on the graph's edges. -/
theorem adjMatrix_ne_zero_iff (i j : Fin n) : m.adjMatrix i j ≠ 0 ↔ m.graph.Adj i j := by
  rw [adj_iff_isSome, adjMatrix_apply]
  rcases m.bondBetween i j with _ | b <;> simp [BondKind.order_ne_zero]

/-- Mathlib's 0/1 adjacency matrix is the indicator of the weighted one. -/
theorem graph_adjMatrix_eq :
    m.graph.adjMatrix ℚ = m.adjMatrix.map fun q ↦ if q = 0 then 0 else 1 := by
  ext i j
  by_cases h : m.adjMatrix i j = 0 <;> simp [h, ← adjMatrix_ne_zero_iff]

/-! ### From the matrix back to the graph

Both `graph` and `adjMatrix` are computed from the bond list; the theorems
above say the two views agree.  This section closes the loop in the other
direction: the weighted matrix determines the graph (`graphOfMatrix`), each
entry is exactly the order of the bond there (`adjMatrix_eq_order_iff`), and
`ofAdjMatrix` decodes a valid matrix back into a molecule whose matrix, graph
and bond kinds are the originals.  What a symmetric matrix cannot carry is
the `src → dst` orientation of each bond and with it the `/` `\` marks, so
`ofAdjMatrix` recovers everything except `Bond.dir`. -/

/-- Mathlib's own round trip, instantiated: the 0/1 adjacency matrix of our
graph determines it. -/
lemma toGraph_adjMatrix : (m.graph.isAdjMatrix_adjMatrix ℚ).toGraph = m.graph :=
  SimpleGraph.toGraph_adjMatrix_eq (G := m.graph) (α := ℚ)

/-- The weighted matrix determines the graph. -/
theorem graphOfMatrix_adjMatrix : graphOfMatrix m.adjMatrix = m.graph := by
  ext i j
  grind [graphOfMatrix_adj, adjMatrix_ne_zero_iff, SimpleGraph.adj_comm, SimpleGraph.Adj.ne]

/-- By `nodup`, the bond `bondBetween` finds is *the* bond on that edge. -/
lemma bondBetween_eq_some_iff {i j : Fin n} {b : Bond n} :
    m.bondBetween i j = some b ↔ b ∈ m.bonds ∧ b.edge = s(i, j) := by
  refine ⟨fun h ↦ ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩,
    fun ⟨hb, he⟩ ↦ ?_⟩
  obtain ⟨b', hb'⟩ : ∃ b', m.bondBetween i j = some b' :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨b, hb, decide_eq_true he⟩)
  have he' : b'.edge = s(i, j) := by simpa using List.find?_some hb'
  rw [hb', List.inj_on_of_nodup_map m.nodup (List.mem_of_find?_eq_some hb') hb (he'.trans he.symm)]

/-- An entry of the weighted matrix is exactly the order of the bond there. -/
theorem adjMatrix_eq_order_iff (i j : Fin n) (k : BondKind) :
    m.adjMatrix i j = k.order ↔ ∃ b ∈ m.bonds, b.edge = s(i, j) ∧ b.kind = k := by
  grind [ofOrder?_adjMatrix, Option.map_eq_some_iff, bondBetween_eq_some_iff,
    BondKind.ofOrder?_order, BondKind.ofOrder?_eq_some]

/-- A molecule's weighted adjacency matrix is a bond matrix. -/
theorem isBondMatrix_adjMatrix : IsBondMatrix m.adjMatrix where
  symm i j := m.isSymm_adjMatrix.apply j i
  diag := m.adjMatrix_apply_self
  entry i j h := by
    rcases hb : m.bondBetween i j with _ | b <;>
      simp_all [adjMatrix_apply, BondKind.order_injective.eq_iff]

/-- The bond that the entry `A i j`, `i < j`, encodes — if it is a bond order. -/
def bondOf (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) : Option (Bond n) :=
  if h : i < j then (BondKind.ofOrder? (A i j)).map fun k ↦ ⟨i, j, k, none, Fin.ne_of_lt h⟩
  else none

/-- `bondOf A i j` is `some b` exactly when `i < j` and `b` is the unmarked `i → j` bond whose
kind has order `A i j`. -/
lemma bondOf_eq_some_iff {A : Matrix (Fin n) (Fin n) ℚ} {i j : Fin n} {b : Bond n} :
    bondOf A i j = some b ↔ i < j ∧ b.src = i ∧ b.dst = j ∧
      BondKind.ofOrder? (A i j) = some b.kind ∧ b.dir = none := by
  obtain ⟨src, dst, kind, dir, ne⟩ := b
  grind [bondOf, Option.map_eq_some_iff]

/-- Every bond a matrix encodes, one per pair `i < j`. -/
def bondsOfMatrix (A : Matrix (Fin n) (Fin n) ℚ) : List (Bond n) :=
  ((List.finRange n) ×ˢ (List.finRange n)).filterMap fun p ↦ bondOf A p.1 p.2

/-- A bond is decoded from `A` exactly when it points from the smaller index to the larger,
carries no direction mark, and its kind's order is its entry. -/
lemma mem_bondsOfMatrix {A : Matrix (Fin n) (Fin n) ℚ} {b : Bond n} :
    b ∈ bondsOfMatrix A ↔
      b.src < b.dst ∧ BondKind.ofOrder? (A b.src b.dst) = some b.kind ∧ b.dir = none := by
  simp [bondsOfMatrix, bondOf_eq_some_iff]

/-- No two decoded bonds join the same pair: `bondsOfMatrix` can be the bond list of a
`Molecule`. -/
lemma nodup_bondsOfMatrix (A : Matrix (Fin n) (Fin n) ℚ) :
    ((bondsOfMatrix A).map Bond.edge).Nodup := by
  refine List.Nodup.map_on ?_ ?_
  · rintro ⟨s, d, k, dir, ne⟩ hb ⟨s', d', k', dir', ne'⟩ hb' he
    grind [mem_bondsOfMatrix, Bond.edge, Sym2.eq_iff]
  · refine ((List.nodup_finRange n).product (List.nodup_finRange n)).filterMap ?_
    rintro ⟨i, j⟩ ⟨i', j'⟩ b hp hp'
    grind [Option.mem_def, bondOf_eq_some_iff]

/-- Decode a weighted adjacency matrix into a molecule with the given atoms; entries
that are zero or not a bond order give no bond. Faithful on `IsBondMatrix` matrices. -/
def ofAdjMatrix (atoms : Vector Atom n) (A : Matrix (Fin n) (Fin n) ℚ) : Molecule n :=
  ⟨atoms, bondsOfMatrix A, nodup_bondsOfMatrix A⟩

/-- Decoding keeps the given atoms. -/
@[simp] lemma atoms_ofAdjMatrix (atoms : Vector Atom n) (A : Matrix (Fin n) (Fin n) ℚ) :
    (ofAdjMatrix atoms A).atoms = atoms := rfl

/-- Where a valid matrix is zero, the decoded molecule has no bond. -/
lemma bondBetween_ofAdjMatrix_eq_none (atoms : Vector Atom n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsBondMatrix A) {i j : Fin n} (h0 : A i j = 0) :
    (ofAdjMatrix atoms A).bondBetween i j = none := by
  simp only [bondBetween, List.find?_eq_none, decide_eq_true_eq]
  intro b hb he
  obtain ⟨-, hk, -⟩ := mem_bondsOfMatrix.mp hb
  grind [BondKind.ofOrder?_eq_some hk, Bond.edge_eq_mk_iff, BondKind.order_ne_zero, hA.symm]

/-- Where a valid matrix is nonzero, the decoded molecule's matrix agrees with it. -/
lemma adjMatrix_ofAdjMatrix_apply_of_ne_zero (atoms : Vector Atom n)
    {A : Matrix (Fin n) (Fin n) ℚ} (hA : IsBondMatrix A) {i j : Fin n} (h0 : A i j ≠ 0) :
    (ofAdjMatrix atoms A).adjMatrix i j = A i j := by
  obtain ⟨k, hk⟩ := hA.entry i j h0
  have hne : i ≠ j := fun h ↦ h0 (h ▸ hA.diag i)
  rw [hk, adjMatrix_eq_order_iff]
  rcases hne.lt_or_gt with hlt | hlt
  · exact ⟨⟨i, j, k, none, hlt.ne⟩, mem_bondsOfMatrix.mpr ⟨hlt, by simp [hk], rfl⟩, rfl, rfl⟩
  · exact ⟨⟨j, i, k, none, hlt.ne⟩, mem_bondsOfMatrix.mpr ⟨hlt, by simp [hA.symm j i, hk], rfl⟩,
      Sym2.eq_swap, rfl⟩

/-- Decoding a valid matrix and re-encoding gives the matrix back. -/
theorem adjMatrix_ofAdjMatrix (atoms : Vector Atom n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsBondMatrix A) : (ofAdjMatrix atoms A).adjMatrix = A := by
  ext i j
  by_cases h0 : A i j = 0
  · simp [adjMatrix_apply, bondBetween_ofAdjMatrix_eq_none atoms hA h0, h0]
  · exact adjMatrix_ofAdjMatrix_apply_of_ne_zero atoms hA h0

/-- The graph of a decoded valid matrix is the matrix's graph. -/
lemma graph_ofAdjMatrix (atoms : Vector Atom n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsBondMatrix A) : (ofAdjMatrix atoms A).graph = graphOfMatrix A := by
  rw [← graphOfMatrix_adjMatrix, adjMatrix_ofAdjMatrix atoms hA]

/-- Round trip: matrix → molecule → matrix. -/
theorem adjMatrix_ofAdjMatrix_adjMatrix :
    (ofAdjMatrix m.atoms m.adjMatrix).adjMatrix = m.adjMatrix :=
  adjMatrix_ofAdjMatrix m.atoms m.isBondMatrix_adjMatrix

/-- Round trip: molecule → matrix → molecule has the same graph. -/
theorem graph_ofAdjMatrix_adjMatrix : (ofAdjMatrix m.atoms m.adjMatrix).graph = m.graph := by
  rw [graph_ofAdjMatrix m.atoms m.isBondMatrix_adjMatrix, graphOfMatrix_adjMatrix]

/-- Round trip: molecule → matrix → molecule has the same bond kinds everywhere. -/
theorem bondKind_ofAdjMatrix_adjMatrix (i j : Fin n) :
    ((ofAdjMatrix m.atoms m.adjMatrix).bondBetween i j).map (·.kind)
      = (m.bondBetween i j).map (·.kind) := by
  rw [← ofOrder?_adjMatrix, ← ofOrder?_adjMatrix, adjMatrix_ofAdjMatrix_adjMatrix]

/-! ### Relabeling is an isomorphism -/

/-- Relabeling transports adjacency: `σ i` and `σ j` are adjacent afterwards exactly when `i`
and `j` were before. -/
lemma relabel_adj_iff (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (m.relabel σ).graph.Adj (σ i) (σ j) ↔ m.graph.Adj i j := by
  simp [adj_iff, bonds_relabel, ← Sym2.map_mk, (Sym2.map.injective σ.injective).eq_iff]

/-- Relabeling the atoms gives an isomorphic molecular graph. -/
def relabelIso (σ : Equiv.Perm (Fin n)) : SimpleGraph.Iso m.graph (m.relabel σ).graph where
  toEquiv := σ
  map_rel_iff' := fun {i j} ↦ m.relabel_adj_iff σ i j

end Molecule

/-- Decode a bond matrix, given the atoms. -/
def BondMatrix.toMolecule (B : BondMatrix n) (atoms : Vector Atom n) : Molecule n :=
  Molecule.ofAdjMatrix atoms B.1

namespace Molecule

variable (m : Molecule n)

/-! ### The molecule's matrices as subtypes, with O(1) lookups -/

/-- The weighted adjacency matrix as a table, each row read off that atom's own
bonds (O(n · bonds) to build, where `adjMatrix` entry by entry would scan the
bond list n² times). -/
def adjTable : Vector (Vector ℚ n) n :=
  Vector.ofFn fun i ↦
    let bs := m.bondsAt i
    Vector.ofFn fun j ↦ ((bs.find? fun b ↦ b.other i == j).map (·.kind.order)).getD 0

/-- The table agrees with `adjMatrix` entry by entry. -/
@[simp] lemma getElem_adjTable (i j : Fin n) : m.adjTable[i.val][j.val] = m.adjMatrix i j := by
  simp [adjTable, find?_bondsAt_other, adjMatrix_apply]

/-- The table, read as a matrix, is `adjMatrix`. -/
lemma of_adjTable_eq_adjMatrix : (Matrix.of fun i j ↦ m.adjTable[i][j]) = m.adjMatrix :=
  Matrix.ext m.getElem_adjTable

/-- The molecule's bond matrix, backed by `adjTable` so that `B i j` is O(1). -/
def toBondMatrix : BondMatrix n :=
  let t := m.adjTable
  ⟨Matrix.of fun i j ↦ t[i][j], m.of_adjTable_eq_adjMatrix ▸ m.isBondMatrix_adjMatrix⟩

/-- The underlying matrix of `toBondMatrix` is `adjMatrix`. -/
@[simp] lemma val_toBondMatrix : m.toBondMatrix.1 = m.adjMatrix := m.of_adjTable_eq_adjMatrix

/-- An entry of `toBondMatrix` is the `adjMatrix` entry: `val_toBondMatrix` pointwise. -/
lemma toBondMatrix_apply (i j : Fin n) : m.toBondMatrix i j = m.adjMatrix i j :=
  congrFun (congrFun m.val_toBondMatrix i) j

/-- The graph of the bond matrix is the molecular graph. -/
@[simp] lemma graph_toBondMatrix : m.toBondMatrix.graph = m.graph := by
  rw [BondMatrix.graph, val_toBondMatrix, graphOfMatrix_adjMatrix]

/-- The bond kind the bond matrix reports is the kind of the bond there. -/
lemma kindAt_toBondMatrix (i j : Fin n) :
    m.toBondMatrix.kindAt i j = (m.bondBetween i j).map (·.kind) := by
  rw [BondMatrix.kindAt, toBondMatrix_apply, ofOrder?_adjMatrix]

/-- The flat 0/1 matrix, from the graph. -/
def toFlatMatrix : FlatMatrix n := ⟨m.graph.adjMatrix ℚ, m.graph.isAdjMatrix_adjMatrix ℚ⟩

/-- Flattening the bond matrix is the graph's own 0/1 matrix. -/
theorem flatten_toBondMatrix : m.toBondMatrix.flatten = m.toFlatMatrix :=
  FlatMatrix.ext fun i j ↦ by simp [toFlatMatrix, graph_adjMatrix_eq]

/-- The graph of the flat matrix is the molecular graph. -/
@[simp] lemma graph_toFlatMatrix : m.toFlatMatrix.graph = m.graph := m.toGraph_adjMatrix

/-! ### Normal form: a molecule that is nothing but atoms and a bond matrix -/

/-- Forget bond orientation and bond-list order: decode the molecule's own
matrix. -/
def normalize : Molecule n := ofAdjMatrix m.atoms m.adjMatrix

/-- Already in normal form. -/
def IsNormal : Prop := m.normalize = m

instance : DecidablePred (IsNormal (n := n)) := fun m ↦
  inferInstanceAs (Decidable (m.normalize = m))

/-- Normalizing keeps the atoms. -/
@[simp] lemma atoms_normalize : m.normalize.atoms = m.atoms := rfl

/-- Normalizing keeps the weighted adjacency matrix. -/
@[simp] lemma adjMatrix_normalize : m.normalize.adjMatrix = m.adjMatrix :=
  m.adjMatrix_ofAdjMatrix_adjMatrix

/-- Normalizing keeps the molecular graph. -/
@[simp] lemma graph_normalize : m.normalize.graph = m.graph :=
  m.graph_ofAdjMatrix_adjMatrix

/-- `normalize` is idempotent, so its image is exactly the molecules in normal form: what
`isNormal_normalize` and `normalEquiv` rest on. -/
theorem normalize_normalize : m.normalize.normalize = m.normalize := by
  simp [normalize, adjMatrix_ofAdjMatrix_adjMatrix]

/-- A normalized molecule is in normal form. -/
lemma isNormal_normalize : m.normalize.IsNormal := m.normalize_normalize

/-- Decoding a valid matrix gives a molecule in normal form. -/
lemma isNormal_ofAdjMatrix (atoms : Vector Atom n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsBondMatrix A) : (ofAdjMatrix atoms A).IsNormal := by
  simp [IsNormal, normalize, adjMatrix_ofAdjMatrix atoms hA]

/-- In normal form, every bond points from the smaller index to the larger
and carries no direction mark. -/
lemma IsNormal.bond_spec {m : Molecule n} (h : m.IsNormal) {b : Bond n} (hb : b ∈ m.bonds) :
    b.src < b.dst ∧ b.dir = none := by
  obtain ⟨hlt, -, hd⟩ := mem_bondsOfMatrix.mp (Eq.symm h ▸ hb : b ∈ m.normalize.bonds)
  exact ⟨hlt, hd⟩

/-- Normalizing keeps the number of bonds: one bond per edge of the graph, before and after. -/
lemma numBonds_normalize : m.normalize.numBonds = m.numBonds := by
  rw [← card_edgeFinset, ← card_edgeFinset, SimpleGraph.edgeFinset_card,
    SimpleGraph.edgeFinset_card]
  exact Fintype.card_congr (Equiv.setCongr (congrArg _ m.graph_normalize))

/-- **Nothing is lost**: molecules in normal form are exactly atoms together
with a bond matrix. -/
def normalEquiv : {m : Molecule n // m.IsNormal} ≃ Vector Atom n × BondMatrix n where
  toFun m := (m.1.atoms, m.1.toBondMatrix)
  invFun p := ⟨p.2.toMolecule p.1, isNormal_ofAdjMatrix p.1 p.2.2⟩
  left_inv m := by
    apply Subtype.ext
    change ofAdjMatrix m.1.atoms m.1.toBondMatrix.1 = m.1
    rw [val_toBondMatrix]
    exact m.2
  right_inv p := by
    refine Prod.ext rfl (BondMatrix.ext fun i j ↦ ?_)
    change (p.2.toMolecule p.1).toBondMatrix.1 i j = p.2.1 i j
    rw [val_toBondMatrix]
    exact congrFun (congrFun (adjMatrix_ofAdjMatrix p.1 p.2.2) i) j

end Molecule

/-! ### Relabeling the matrix views -/

namespace Molecule

variable (m : Molecule n)

/-- The bond between `σ i` and `σ j` after relabeling is the bond between `i` and `j`,
relabeled. -/
lemma bondBetween_relabel (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (m.relabel σ).bondBetween (σ i) (σ j) = (m.bondBetween i j).map (Bond.map σ σ.injective) := by
  simp [bondBetween, bonds_relabel, List.find?_map, Function.comp_def, ← Sym2.map_mk,
    (Sym2.map.injective σ.injective).eq_iff]

/-- The weighted matrix of a relabeled molecule at `(σ i, σ j)` is the original's at `(i, j)`. -/
lemma adjMatrix_relabel_apply (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (m.relabel σ).adjMatrix (σ i) (σ j) = m.adjMatrix i j := by
  simp [adjMatrix_apply, bondBetween_relabel, Function.comp_def]

/-- Relabeling a molecule relabels its bond matrix. -/
theorem toBondMatrix_relabel (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).toBondMatrix = m.toBondMatrix.relabel σ :=
  BondMatrix.ext fun i j ↦ by simpa using m.adjMatrix_relabel_apply σ (σ.symm i) (σ.symm j)

end Molecule

/-! ### A molecule as atoms and a bond matrix -/

/-- A molecule as the canonical search sees it: its atoms and its bond matrix —
a molecule up to the order and orientation of its bond list (`normalEquiv`).
The matrix is stored as a table, so a lookup is O(1) wherever the value flows
(a matrix closing over a table is not: the compiler may float the table into
the closure and rebuild it per call); `bonds` is the same matrix as a
`BondMatrix` for the theorems.  Relabeling acts on it literally, so an
automorphism is an equality `d.relabel γ = d`. -/
structure MolData (n : ℕ) where
  /-- The atoms. -/
  atoms : Vector Atom n
  /-- The weighted adjacency matrix, as a table. -/
  table : Vector (Vector ℚ n) n
  /-- The table is a bond matrix. -/
  isBondMatrix : IsBondMatrix (Matrix.of fun i j : Fin n ↦ table[i][j])

namespace MolData

variable (d : MolData n)

/-- Two `MolData` with the same atoms and the same table are equal: the proof field carries no
data. Tagged `@[ext]`, so `ext` reduces an equality of `MolData` to those two components. -/
@[ext] lemma ext {d d' : MolData n} (ha : d.atoms = d'.atoms) (ht : d.table = d'.table) :
    d = d' := by
  cases d
  cases d'
  congr

instance : DecidableEq (MolData n) := fun d d' ↦
  decidable_of_iff (d.atoms = d'.atoms ∧ d.table = d'.table)
    ⟨fun ⟨h1, h2⟩ ↦ ext h1 h2, fun h ↦ h ▸ ⟨rfl, rfl⟩⟩

/-- The bond matrix. -/
def bonds : BondMatrix n := ⟨Matrix.of fun i j ↦ d.table[i][j], d.isBondMatrix⟩

/-- An entry of the bond matrix is the table entry. -/
@[simp] lemma bonds_apply (i j : Fin n) : d.bonds i j = d.table[i][j] := rfl

/-- Relabel the atoms by `σ`: position `σ i` receives what `i` had. -/
def relabel (σ : Equiv.Perm (Fin n)) : MolData n where
  atoms := relabelVec σ d.atoms
  table := Vector.ofFn fun i ↦ Vector.ofFn fun j ↦ d.table[σ.symm i][σ.symm j]
  isBondMatrix :=
    { symm := fun i j ↦ by
        simpa [Vector.getElem_ofFn] using d.isBondMatrix.symm (σ.symm i) (σ.symm j)
      diag := fun i ↦ by simpa [Vector.getElem_ofFn] using d.isBondMatrix.diag (σ.symm i)
      entry := fun i j h ↦ by
        simp only [Matrix.of_apply, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] at h ⊢
        exact d.isBondMatrix.entry _ _ h }

/-- Relabeling `MolData` relabels its atoms by `relabelVec`. -/
@[simp] lemma atoms_relabel (σ : Equiv.Perm (Fin n)) : (d.relabel σ).atoms = relabelVec σ d.atoms :=
  rfl

/-- Entry `(i, j)` of the relabeled table is entry `(σ⁻¹ i, σ⁻¹ j)` of the original. -/
@[simp] lemma table_relabel (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (d.relabel σ).table[i][j] = d.table[σ.symm i][σ.symm j] := by
  simp [relabel]

/-- Relabeling `MolData` relabels its bond matrix. -/
lemma bonds_relabel (σ : Equiv.Perm (Fin n)) : (d.relabel σ).bonds = d.bonds.relabel σ :=
  BondMatrix.ext fun i j ↦ by simp [relabel]

/-- Two relabelings in a row are one relabeling along the composite: first `σ`, then `τ`. -/
lemma relabel_relabel (σ τ : Equiv.Perm (Fin n)) :
    (d.relabel σ).relabel τ = d.relabel (σ.trans τ) :=
  ext (relabelVec_relabelVec σ τ d.atoms) <| Vector.ext fun i hi ↦ Vector.ext fun j hj ↦ by
    simp [relabel, Vector.getElem_ofFn]

/-- The molecule, in normal form. -/
def toMolecule : Molecule n := Molecule.ofAdjMatrix d.atoms d.bonds.1

end MolData

namespace Molecule

variable (m : Molecule n)

/-- The atoms and the bond matrix, as a table with O(1) lookups. -/
def toMolData : MolData n :=
  ⟨m.atoms, m.adjTable, m.of_adjTable_eq_adjMatrix ▸ m.isBondMatrix_adjMatrix⟩

/-- A molecule's data has the molecule's atoms. -/
@[simp] lemma toMolData_atoms : m.toMolData.atoms = m.atoms := rfl

/-- The bond matrix of a molecule's data is `toBondMatrix`, definitionally. -/
lemma toMolData_bonds : m.toMolData.bonds = m.toBondMatrix := rfl

/-- Taking a molecule's data commutes with relabeling. -/
lemma toMolData_relabel (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).toMolData = m.toMolData.relabel σ := by
  refine MolData.ext rfl ?_
  ext i hi j hj
  simpa [toMolData, MolData.relabel, Vector.getElem_ofFn,
    getElem_adjTable (m.relabel σ) ⟨i, hi⟩ ⟨j, hj⟩]
    using m.adjMatrix_relabel_apply σ (σ.symm ⟨i, hi⟩) (σ.symm ⟨j, hj⟩)

/-- Round trip: the molecule of a molecule's data is its normal form. -/
lemma toMolecule_toMolData : m.toMolData.toMolecule = m.normalize := by
  simp [MolData.toMolecule, toMolData_bonds, normalize]

end Molecule

/-- Normal form of a bundled molecule. -/
def Mol.normalize (M : Mol) : Mol := ⟨M.n, M.mol.normalize⟩

/-- Whether a bundled molecule is in normal form. -/
def Mol.isNormal (M : Mol) : Bool := decide M.mol.IsNormal

end LeanSMILES
