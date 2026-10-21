import LeanSMILES.Chem.Molecule
import LeanSMILES.SMILES.Canon
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# LeanSMILES.Chem.Graph

The two mathematical views of a `Molecule n`:

* `Molecule.graph : SimpleGraph (Fin n)` — Mathlib's simple graph on the atom
  indices, adjacent when some bond joins them.  It has decidable adjacency, so
  all of Mathlib's finite-graph machinery (`degree`, `edgeFinset`, the
  handshake lemma, `adjMatrix`) is available and computable.
* `Molecule.adjMatrix : Matrix (Fin n) (Fin n) ℚ` — the bond-order-weighted
  adjacency matrix, symmetric with zero diagonal; it is nonzero exactly where
  the graph is adjacent, and Mathlib's 0/1 `adjMatrix` is its indicator.

Relabelling the atoms by a permutation gives an isomorphic graph
(`relabelIso`) — which is what makes canonicalisation (`LeanSMILES.SMILES.Canon`)
a change of *labels* and nothing else.
-/

namespace LeanSMILES.Molecule

variable {n : ℕ} (m : Molecule n)

/-! ### The simple graph -/

/-- The molecular graph: atoms are adjacent when some bond joins them. -/
def graph : SimpleGraph (Fin n) where
  Adj i j := s(i, j) ∈ m.edges
  symm := by
    intro i j h
    rwa [Sym2.eq_swap]
  loopless := ⟨fun i h => by
    obtain ⟨b, -, hb⟩ := List.mem_map.mp h
    exact b.edge_ne_diag i hb⟩

instance : DecidableRel m.graph.Adj :=
  fun i j => inferInstanceAs (Decidable (s(i, j) ∈ m.edges))

theorem adj_iff (i j : Fin n) : m.graph.Adj i j ↔ ∃ b ∈ m.bonds, b.edge = s(i, j) := by
  change s(i, j) ∈ m.edges ↔ _
  simp [edges, List.mem_map]

/-- Mathlib's edge set is exactly the bond list. -/
theorem edgeFinset_eq : m.graph.edgeFinset = m.edges.toFinset := by
  ext e
  refine Sym2.ind (fun i j => ?_) e
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

theorem bondBetween_symm (i j : Fin n) : m.bondBetween i j = m.bondBetween j i := by
  unfold bondBetween
  congr 1
  funext b
  rw [@Sym2.eq_swap _ i j]

theorem bondBetween_self (i : Fin n) : m.bondBetween i i = none := by
  unfold bondBetween
  rw [List.find?_eq_none]
  intro b _ hb
  exact b.edge_ne_diag i (of_decide_eq_true hb)

theorem adj_iff_isSome (i j : Fin n) : m.graph.Adj i j ↔ (m.bondBetween i j).isSome := by
  simp only [adj_iff, bondBetween, List.find?_isSome, decide_eq_true_eq]

/-- The bond-order-weighted adjacency matrix, over `ℚ`. -/
def adjMatrix : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => ((m.bondBetween i j).map (·.kind.order)).getD 0

theorem adjMatrix_apply (i j : Fin n) :
    m.adjMatrix i j = ((m.bondBetween i j).map (·.kind.order)).getD 0 := rfl

theorem adjMatrix_isSymm : m.adjMatrix.IsSymm :=
  Matrix.IsSymm.ext fun i j => by rw [adjMatrix_apply, adjMatrix_apply, bondBetween_symm]

@[simp] theorem adjMatrix_self (i : Fin n) : m.adjMatrix i i = 0 := by
  rw [adjMatrix_apply, bondBetween_self]
  rfl

/-- The weighted matrix is nonzero exactly on the graph's edges. -/
theorem adjMatrix_ne_zero_iff (i j : Fin n) : m.adjMatrix i j ≠ 0 ↔ m.graph.Adj i j := by
  rw [adj_iff_isSome, adjMatrix_apply]
  rcases hb : m.bondBetween i j with _ | b <;> simp [BondKind.order_ne_zero]

/-- Mathlib's 0/1 adjacency matrix is the indicator of the weighted one. -/
theorem graph_adjMatrix_eq :
    m.graph.adjMatrix ℚ = m.adjMatrix.map fun q => if q = 0 then 0 else 1 := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply, Matrix.map_apply]
  by_cases h : m.graph.Adj i j
  · have := (m.adjMatrix_ne_zero_iff i j).mpr h
    simp [h, this]
  · have : m.adjMatrix i j = 0 := by
      by_contra hne
      exact h ((m.adjMatrix_ne_zero_iff i j).mp hne)
    simp [h, this]

/-! ### Relabelling is an isomorphism -/

theorem relabel_adj_iff (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (m.relabel σ).graph.Adj (σ i) (σ j) ↔ m.graph.Adj i j := by
  change s(σ i, σ j) ∈ (m.relabel σ).edges ↔ s(i, j) ∈ m.edges
  rw [edges_relabel, ← Sym2.map_mk, List.mem_map_of_injective (Sym2.map.injective σ.injective)]

/-- Relabelling the atoms gives an isomorphic molecular graph. -/
def relabelIso (σ : Equiv.Perm (Fin n)) : SimpleGraph.Iso m.graph (m.relabel σ).graph where
  toEquiv := σ
  map_rel_iff' := fun {i j} => m.relabel_adj_iff σ i j

/-- Canonicalization (`LeanSMILES.SMILES.Canon`) changes labels and nothing
else: the canonical molecule's graph is isomorphic to the original's. -/
def canonicalize_iso (budget : ℕ := 1024) :
    SimpleGraph.Iso m.graph (m.canonicalize budget).graph :=
  m.relabelIso _

end LeanSMILES.Molecule
