/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
import LeanSMILES.Chem.Molecule
import LeanSMILES.Chem.BondMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

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

lemma adj_iff (i j : Fin n) : m.graph.Adj i j ↔ ∃ b ∈ m.bonds, b.edge = s(i, j) := by
  change s(i, j) ∈ m.edges ↔ _
  simp [edges, List.mem_map]

/-- Mathlib's edge set is exactly the bond list. -/
lemma edgeFinset_eq : m.graph.edgeFinset = m.edges.toFinset := by
  ext e
  refine Sym2.ind (fun i j ↦ ?_) e
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, List.mem_toFinset]
  rfl

/-- Because no two bonds join the same atoms, Mathlib counts the bonds. -/
theorem card_edgeFinset : m.graph.edgeFinset.card = m.numBonds := by
  rw [edgeFinset_eq, edges, List.toFinset_card_of_nodup m.nodup, List.length_map, numBonds]

/-- The handshake lemma, for molecules: degrees sum to twice the bond count. -/
theorem sum_degrees : ∑ i, m.graph.degree i = 2 * m.numBonds := by
  rw [← card_edgeFinset]
  exact m.graph.sum_degrees_eq_twice_card_edges

/-! ### The adjacency matrix -/

lemma bondBetween_symm (i j : Fin n) : m.bondBetween i j = m.bondBetween j i := by
  unfold bondBetween
  congr 1
  funext b
  rw [@Sym2.eq_swap _ i j]

lemma bondBetween_self (i : Fin n) : m.bondBetween i i = none := by
  unfold bondBetween
  rw [List.find?_eq_none]
  intro b _ hb
  exact b.edge_ne_diag i (of_decide_eq_true hb)

lemma adj_iff_isSome (i j : Fin n) : m.graph.Adj i j ↔ (m.bondBetween i j).isSome := by
  simp only [adj_iff, bondBetween, List.find?_isSome, decide_eq_true_eq]

/-- The bond-order-weighted adjacency matrix, over `ℚ`. -/
def adjMatrix : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j ↦ ((m.bondBetween i j).map (·.kind.order)).getD 0

lemma adjMatrix_apply (i j : Fin n) :
    m.adjMatrix i j = ((m.bondBetween i j).map (·.kind.order)).getD 0 := rfl

lemma isSymm_adjMatrix : m.adjMatrix.IsSymm :=
  Matrix.IsSymm.ext fun i j ↦ by rw [adjMatrix_apply, adjMatrix_apply, bondBetween_symm]

@[simp] lemma adjMatrix_apply_self (i : Fin n) : m.adjMatrix i i = 0 := by
  rw [adjMatrix_apply, bondBetween_self]
  rfl

/-- The weighted matrix is nonzero exactly on the graph's edges. -/
theorem adjMatrix_ne_zero_iff (i j : Fin n) : m.adjMatrix i j ≠ 0 ↔ m.graph.Adj i j := by
  rw [adj_iff_isSome, adjMatrix_apply]
  rcases hb : m.bondBetween i j with _ | b <;> simp [BondKind.order_ne_zero]

/-- Mathlib's 0/1 adjacency matrix is the indicator of the weighted one. -/
theorem graph_adjMatrix_eq :
    m.graph.adjMatrix ℚ = m.adjMatrix.map fun q ↦ if q = 0 then 0 else 1 := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply, Matrix.map_apply]
  by_cases h : m.graph.Adj i j
  · have := (m.adjMatrix_ne_zero_iff i j).mpr h
    simp [h, this]
  · have : m.adjMatrix i j = 0 := by
      by_contra hne
      exact h ((m.adjMatrix_ne_zero_iff i j).mp hne)
    simp [h, this]

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
  rw [graphOfMatrix_adj, adjMatrix_ne_zero_iff, adjMatrix_ne_zero_iff]
  exact ⟨fun ⟨_, h⟩ ↦ h.elim id (fun h' ↦ m.graph.symm h'),
    fun h ↦ ⟨m.graph.ne_of_adj h, Or.inl h⟩⟩

/-- By `nodup`, the bond `bondBetween` finds is *the* bond on that edge. -/
lemma bondBetween_eq_some_iff {i j : Fin n} {b : Bond n} :
    m.bondBetween i j = some b ↔ b ∈ m.bonds ∧ b.edge = s(i, j) := by
  unfold bondBetween
  constructor
  · intro h
    have hp := List.find?_some h
    exact ⟨List.mem_of_find?_eq_some h, of_decide_eq_true hp⟩
  · rintro ⟨hb, he⟩
    have hs : (m.bonds.find? fun b ↦ decide (b.edge = s(i, j))).isSome := by
      rw [List.find?_isSome]
      exact ⟨b, hb, decide_eq_true he⟩
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp hs
    have hm' := List.mem_of_find?_eq_some hb'
    have hp' := List.find?_some hb'
    have he' : b'.edge = s(i, j) := of_decide_eq_true hp'
    rw [hb', List.inj_on_of_nodup_map m.nodup hm' hb (he'.trans he.symm)]

/-- An entry of the weighted matrix is exactly the order of the bond there. -/
theorem adjMatrix_eq_order_iff (i j : Fin n) (k : BondKind) :
    m.adjMatrix i j = k.order ↔ ∃ b ∈ m.bonds, b.edge = s(i, j) ∧ b.kind = k := by
  rw [adjMatrix_apply]
  constructor
  · intro h
    rcases hb : m.bondBetween i j with _ | b
    · rw [hb] at h
      simp only [Option.map_none, Option.getD_none] at h
      exact absurd h.symm k.order_ne_zero
    · rw [hb] at h
      simp only [Option.map_some, Option.getD_some] at h
      obtain ⟨hm, he⟩ := m.bondBetween_eq_some_iff.mp hb
      exact ⟨b, hm, he, BondKind.order_injective h⟩
  · rintro ⟨b, hb, he, rfl⟩
    rw [m.bondBetween_eq_some_iff.mpr ⟨hb, he⟩]
    rfl

/-- A molecule's weighted adjacency matrix is a bond matrix. -/
theorem isBondMatrix_adjMatrix : IsBondMatrix m.adjMatrix where
  symm i j := by rw [adjMatrix_apply, adjMatrix_apply, bondBetween_symm]
  diag := m.adjMatrix_apply_self
  entry i j h := by
    rw [adjMatrix_apply] at h ⊢
    rcases hb : m.bondBetween i j with _ | b
    · rw [hb] at h
      simp at h
    · exact ⟨b.kind, by simp⟩

/-- The bond that the entry `A i j`, `i < j`, encodes — if it is a bond order. -/
def bondOf (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) : Option (Bond n) :=
  if h : i < j then (BondKind.ofOrder? (A i j)).map fun k ↦ ⟨i, j, k, none, Fin.ne_of_lt h⟩
  else none

lemma bondOf_eq_some_iff {A : Matrix (Fin n) (Fin n) ℚ} {i j : Fin n} {b : Bond n} :
    bondOf A i j = some b ↔ i < j ∧ b.src = i ∧ b.dst = j ∧
      BondKind.ofOrder? (A i j) = some b.kind ∧ b.dir = none := by
  unfold bondOf
  split_ifs with h
  · rw [Option.map_eq_some_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨h, rfl, rfl, hk, rfl⟩
    · rintro ⟨-, rfl, rfl, hk, hd⟩
      refine ⟨b.kind, hk, ?_⟩
      obtain ⟨src, dst, kind, dir, ne⟩ := b
      simp only at hd
      subst hd
      rfl
  · simp [h]

/-- Every bond a matrix encodes, one per pair `i < j`. -/
def bondsOfMatrix (A : Matrix (Fin n) (Fin n) ℚ) : List (Bond n) :=
  ((List.finRange n) ×ˢ (List.finRange n)).filterMap fun p ↦ bondOf A p.1 p.2

lemma mem_bondsOfMatrix {A : Matrix (Fin n) (Fin n) ℚ} {b : Bond n} :
    b ∈ bondsOfMatrix A ↔
      b.src < b.dst ∧ BondKind.ofOrder? (A b.src b.dst) = some b.kind ∧ b.dir = none := by
  unfold bondsOfMatrix
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨i, j⟩, -, h⟩
    obtain ⟨hlt, rfl, rfl, hk, hd⟩ := bondOf_eq_some_iff.mp h
    exact ⟨hlt, hk, hd⟩
  · rintro ⟨hlt, hk, hd⟩
    exact ⟨(b.src, b.dst), by simp, bondOf_eq_some_iff.mpr ⟨hlt, rfl, rfl, hk, hd⟩⟩

lemma nodup_bondsOfMatrix (A : Matrix (Fin n) (Fin n) ℚ) :
    ((bondsOfMatrix A).map Bond.edge).Nodup := by
  refine List.Nodup.map_on ?_ ?_
  · intro b hb b' hb' he
    obtain ⟨hlt, hk, hd⟩ := mem_bondsOfMatrix.mp hb
    obtain ⟨hlt', hk', hd'⟩ := mem_bondsOfMatrix.mp hb'
    have he' : b.edge = s(b'.src, b'.dst) := he
    rcases Bond.edge_eq_mk_iff.mp he' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨s, d, k, dir, ne⟩ := b
      obtain ⟨s', d', k', dir', ne'⟩ := b'
      simp only at h1 h2 hk hk' hd hd'
      subst h1 h2 hd hd'
      rw [hk] at hk'
      cases hk'
      rfl
    · rw [h1, h2] at hlt
      exact absurd hlt (lt_asymm hlt')
  · refine ((List.nodup_finRange n).product (List.nodup_finRange n)).filterMap ?_
    intro p p' b hp hp'
    rw [Option.mem_def] at hp hp'
    obtain ⟨-, h1, h2, -, -⟩ := bondOf_eq_some_iff.mp hp
    obtain ⟨-, h1', h2', -, -⟩ := bondOf_eq_some_iff.mp hp'
    exact Prod.ext (h1.symm.trans h1') (h2.symm.trans h2')

/-- Decode a weighted adjacency matrix into a molecule with the given atoms; entries
that are zero or not a bond order give no bond. Faithful on `IsBondMatrix` matrices. -/
def ofAdjMatrix (atoms : Vector Atom n) (A : Matrix (Fin n) (Fin n) ℚ) : Molecule n :=
  ⟨atoms, bondsOfMatrix A, nodup_bondsOfMatrix A⟩

@[simp] lemma atoms_ofAdjMatrix (atoms : Vector Atom n) (A : Matrix (Fin n) (Fin n) ℚ) :
    (ofAdjMatrix atoms A).atoms = atoms := rfl

/-- Where a valid matrix is zero, the decoded molecule has no bond. -/
lemma bondBetween_ofAdjMatrix_eq_none (atoms : Vector Atom n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsBondMatrix A) {i j : Fin n} (h0 : A i j = 0) :
    (ofAdjMatrix atoms A).bondBetween i j = none := by
  unfold bondBetween
  rw [List.find?_eq_none]
  intro b hb hbe
  have he := of_decide_eq_true hbe
  obtain ⟨-, hk, -⟩ := mem_bondsOfMatrix.mp hb
  have hq := BondKind.ofOrder?_eq_some hk
  rcases Bond.edge_eq_mk_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact b.kind.order_ne_zero (hq.symm.trans h0)
  · exact b.kind.order_ne_zero (hq.symm.trans ((hA.symm _ _).trans h0))

/-- Where a valid matrix is nonzero, the decoded molecule's matrix agrees with it. -/
lemma adjMatrix_ofAdjMatrix_apply_of_ne_zero (atoms : Vector Atom n)
    {A : Matrix (Fin n) (Fin n) ℚ} (hA : IsBondMatrix A) {i j : Fin n} (h0 : A i j ≠ 0) :
    (ofAdjMatrix atoms A).adjMatrix i j = A i j := by
  obtain ⟨k, hk⟩ := hA.entry i j h0
  have hne : i ≠ j := fun h ↦ h0 (h ▸ hA.diag i)
  rw [adjMatrix_apply]
  rcases lt_trichotomy i j with hlt | heq | hlt
  · have hb₀ : (⟨i, j, k, none, Fin.ne_of_lt hlt⟩ : Bond n) ∈ bondsOfMatrix A :=
      mem_bondsOfMatrix.mpr ⟨hlt, by rw [hk, BondKind.ofOrder?_order], rfl⟩
    rw [(ofAdjMatrix atoms A).bondBetween_eq_some_iff.mpr ⟨hb₀, rfl⟩]
    simp [hk]
  · exact absurd heq hne
  · have hk' : A j i = k.order := (hA.symm j i).trans hk
    have hb₀ : (⟨j, i, k, none, Fin.ne_of_lt hlt⟩ : Bond n) ∈ bondsOfMatrix A :=
      mem_bondsOfMatrix.mpr ⟨hlt, by rw [hk', BondKind.ofOrder?_order], rfl⟩
    rw [(ofAdjMatrix atoms A).bondBetween_eq_some_iff.mpr ⟨hb₀, Sym2.eq_swap⟩]
    simp [hk]

/-- Decoding a valid matrix and re-encoding gives the matrix back. -/
theorem adjMatrix_ofAdjMatrix (atoms : Vector Atom n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsBondMatrix A) : (ofAdjMatrix atoms A).adjMatrix = A := by
  ext i j
  by_cases h0 : A i j = 0
  · rw [adjMatrix_apply, bondBetween_ofAdjMatrix_eq_none atoms hA h0, h0]
    rfl
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
  have hM := congrFun (congrFun m.adjMatrix_ofAdjMatrix_adjMatrix i) j
  rw [adjMatrix_apply, adjMatrix_apply] at hM
  rcases h₁ : (ofAdjMatrix m.atoms m.adjMatrix).bondBetween i j with _ | b <;>
    rcases h₂ : m.bondBetween i j with _ | b'
  · rfl
  · rw [h₁, h₂] at hM
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] at hM
    exact absurd hM.symm b'.kind.order_ne_zero
  · rw [h₁, h₂] at hM
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] at hM
    exact absurd hM b.kind.order_ne_zero
  · rw [h₁, h₂] at hM
    simp only [Option.map_some, Option.getD_some] at hM
    simp only [Option.map_some, BondKind.order_injective hM]

/-! ### Relabeling is an isomorphism -/

lemma relabel_adj_iff (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (m.relabel σ).graph.Adj (σ i) (σ j) ↔ m.graph.Adj i j := by
  change s(σ i, σ j) ∈ (m.relabel σ).edges ↔ s(i, j) ∈ m.edges
  rw [edges_relabel, ← Sym2.map_mk, List.mem_map_of_injective (Sym2.map.injective σ.injective)]

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

/-- The weighted adjacency matrix as a table. -/
def adjTable : Vector (Vector ℚ n) n :=
  Vector.ofFn fun i ↦ Vector.ofFn fun j ↦ m.adjMatrix i j

@[simp] lemma getElem_adjTable (i j : Fin n) : m.adjTable[i.val][j.val] = m.adjMatrix i j := by
  simp [adjTable]

lemma of_adjTable_eq_adjMatrix : (Matrix.of fun i j ↦ m.adjTable[i][j]) = m.adjMatrix := by
  ext i j
  rw [Matrix.of_apply]
  exact m.getElem_adjTable i j

/-- The molecule's bond matrix, backed by `adjTable` so that `B i j` is O(1). -/
def toBondMatrix : BondMatrix n :=
  let t := m.adjTable
  ⟨Matrix.of fun i j ↦ t[i][j], m.of_adjTable_eq_adjMatrix ▸ m.isBondMatrix_adjMatrix⟩

@[simp] lemma val_toBondMatrix : m.toBondMatrix.1 = m.adjMatrix := m.of_adjTable_eq_adjMatrix

lemma toBondMatrix_apply (i j : Fin n) : m.toBondMatrix i j = m.adjMatrix i j :=
  congrFun (congrFun m.val_toBondMatrix i) j

@[simp] lemma graph_toBondMatrix : m.toBondMatrix.graph = m.graph := by
  unfold BondMatrix.graph
  rw [val_toBondMatrix, graphOfMatrix_adjMatrix]

lemma kindAt_toBondMatrix (i j : Fin n) :
    m.toBondMatrix.kindAt i j = (m.bondBetween i j).map (·.kind) := by
  unfold BondMatrix.kindAt
  rw [toBondMatrix_apply, adjMatrix_apply]
  rcases m.bondBetween i j with _ | b
  · norm_num [BondKind.ofOrder?]
  · simp

/-- The flat 0/1 matrix, from the graph. -/
def toFlatMatrix : FlatMatrix n := ⟨m.graph.adjMatrix ℚ, m.graph.isAdjMatrix_adjMatrix ℚ⟩

/-- Flattening the bond matrix is the graph's own 0/1 matrix. -/
theorem flatten_toBondMatrix : m.toBondMatrix.flatten = m.toFlatMatrix := by
  apply FlatMatrix.ext
  intro i j
  change (if m.toBondMatrix i j = 0 then 0 else 1) = m.graph.adjMatrix ℚ i j
  rw [toBondMatrix_apply, m.graph_adjMatrix_eq, Matrix.map_apply]

@[simp] lemma graph_toFlatMatrix : m.toFlatMatrix.graph = m.graph := m.toGraph_adjMatrix

/-! ### Normal form: a molecule that is nothing but atoms and a bond matrix -/

/-- Forget bond orientation and bond-list order: decode the molecule's own
matrix. -/
def normalize : Molecule n := ofAdjMatrix m.atoms m.adjMatrix

/-- Already in normal form. -/
def IsNormal : Prop := m.normalize = m

@[ext] lemma ext {m m' : Molecule n} (ha : m.atoms = m'.atoms) (hb : m.bonds = m'.bonds) :
    m = m' := by
  cases m
  cases m'
  cases ha
  cases hb
  rfl

instance : DecidableEq (Molecule n) := fun m m' ↦
  decidable_of_iff (m.atoms = m'.atoms ∧ m.bonds = m'.bonds)
    ⟨fun ⟨h1, h2⟩ ↦ ext h1 h2, fun h ↦ h ▸ ⟨rfl, rfl⟩⟩

instance : DecidablePred (IsNormal (n := n)) := fun m ↦
  inferInstanceAs (Decidable (m.normalize = m))

@[simp] lemma atoms_normalize : m.normalize.atoms = m.atoms := rfl

@[simp] lemma adjMatrix_normalize : m.normalize.adjMatrix = m.adjMatrix :=
  m.adjMatrix_ofAdjMatrix_adjMatrix

@[simp] lemma graph_normalize : m.normalize.graph = m.graph :=
  m.graph_ofAdjMatrix_adjMatrix

theorem normalize_normalize : m.normalize.normalize = m.normalize := by
  unfold normalize
  rw [atoms_ofAdjMatrix, adjMatrix_ofAdjMatrix_adjMatrix]

lemma isNormal_normalize : m.normalize.IsNormal := m.normalize_normalize

lemma isNormal_ofAdjMatrix (atoms : Vector Atom n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsBondMatrix A) : (ofAdjMatrix atoms A).IsNormal := by
  unfold IsNormal normalize
  rw [atoms_ofAdjMatrix, adjMatrix_ofAdjMatrix atoms hA]

/-- In normal form, every bond points from the smaller index to the larger
and carries no direction mark. -/
lemma IsNormal.bond_spec {m : Molecule n} (h : m.IsNormal) {b : Bond n} (hb : b ∈ m.bonds) :
    b.src < b.dst ∧ b.dir = none := by
  have h' : b ∈ m.normalize.bonds := by
    rw [show m.normalize = m from h]
    exact hb
  obtain ⟨hlt, -, hd⟩ := mem_bondsOfMatrix.mp h'
  exact ⟨hlt, hd⟩

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

/-- Normal form of a bundled molecule. -/
def Mol.normalize (M : Mol) : Mol := ⟨M.n, M.mol.normalize⟩

/-- Whether a bundled molecule is in normal form. -/
def Mol.isNormal (M : Mol) : Bool := decide M.mol.IsNormal

end LeanSMILES
