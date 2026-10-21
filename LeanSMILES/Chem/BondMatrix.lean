import LeanSMILES.Chem.Graph

/-!
# LeanSMILES.Chem.BondMatrix

Two matrix representations of a molecule, each a *subtype* of Mathlib's
`Matrix` so that "this matrix comes from a molecule" is in the type:

* `BondMatrix n := {A : Matrix (Fin n) (Fin n) ℚ // IsBondMatrix A}` — the
  weighted adjacency matrix: symmetric, zero on the diagonal, every nonzero
  entry a bond order (aromatic `3/2`).  It remembers the bond kinds.
* `FlatMatrix n := {A : Matrix (Fin n) (Fin n) ℚ // A.IsAdjMatrix}` — the 0/1
  adjacency matrix, Mathlib's `Matrix.IsAdjMatrix`.  It remembers adjacency
  only, and is what spectral and walk-counting arguments want.

`Molecule.toBondMatrix` is backed by a materialized table, so `B i j` is an
O(1) lookup (what descriptor code wants), while the theorems speak about the
same matrix as `Molecule.adjMatrix`.

**Nothing is lost.**  What a symmetric matrix cannot hold is the `src → dst`
orientation of a bond (the `/` `\` marks) and the order of the bond list.
`Molecule.normalize` forgets exactly those, `IsNormal` says a molecule has
already forgotten them, and `normalEquiv` is the theorem: normal molecules
are *exactly* atoms together with a bond matrix.
-/

namespace LeanSMILES

open Molecule

/-! ### The weighted bond matrix -/

/-- A weighted adjacency matrix that comes from a molecule. -/
def BondMatrix (n : ℕ) := {A : Matrix (Fin n) (Fin n) ℚ // IsBondMatrix A}

namespace BondMatrix

variable {n : ℕ}

instance : CoeFun (BondMatrix n) (fun _ => Fin n → Fin n → ℚ) := ⟨fun B => B.1⟩

def toMatrix (B : BondMatrix n) : Matrix (Fin n) (Fin n) ℚ := B.1

theorem symm (B : BondMatrix n) (i j : Fin n) : B i j = B j i := B.2.symm i j

theorem diag (B : BondMatrix n) (i : Fin n) : B i i = 0 := B.2.diag i

theorem entry (B : BondMatrix n) (i j : Fin n) (h : B i j ≠ 0) : ∃ k : BondKind, B i j = k.order :=
  B.2.entry i j h

theorem ext {B B' : BondMatrix n} (h : ∀ i j, B i j = B' i j) : B = B' :=
  Subtype.ext (Matrix.ext h)

/-- The bond kind between `i` and `j`, if they are bonded. -/
def kindAt (B : BondMatrix n) (i j : Fin n) : Option BondKind := BondKind.ofOrder? (B i j)

theorem kindAt_eq_some_iff {B : BondMatrix n} {i j : Fin n} {k : BondKind} :
    B.kindAt i j = some k ↔ B i j = k.order :=
  ⟨BondKind.ofOrder?_eq_some, fun h => by rw [kindAt, h, BondKind.ofOrder?_order]⟩

/-- The graph of the nonzero entries. -/
def graph (B : BondMatrix n) : SimpleGraph (Fin n) := graphOfMatrix B.1

/-- Decode, given the atoms. -/
def toMolecule (B : BondMatrix n) (atoms : Vector Atom n) : Molecule n := ofAdjMatrix atoms B.1

/-! #### Checking an arbitrary matrix -/

/-- Executable test for `IsBondMatrix`. -/
def check (A : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  (List.finRange n).all fun i =>
    A i i == 0 && (List.finRange n).all fun j =>
      A i j == A j i && (A i j == 0 || (BondKind.ofOrder? (A i j)).isSome)

theorem check_iff {A : Matrix (Fin n) (Fin n) ℚ} : check A = true ↔ IsBondMatrix A := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    beq_iff_eq, Bool.or_eq_true]
  constructor
  · intro h
    refine ⟨fun i j => ((h i).2 j).1, fun i => (h i).1, fun i j hij => ?_⟩
    rcases ((h i).2 j).2 with h0 | hs
    · exact absurd h0 hij
    · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
      exact ⟨k, BondKind.ofOrder?_eq_some hk⟩
  · intro hA i
    refine ⟨hA.diag i, fun j => ⟨hA.symm i j, ?_⟩⟩
    by_cases h0 : A i j = 0
    · exact Or.inl h0
    · obtain ⟨k, hk⟩ := hA.entry i j h0
      right
      rw [hk, BondKind.ofOrder?_order]
      rfl

instance : DecidablePred (IsBondMatrix (n := n)) := fun _ => decidable_of_iff _ check_iff

/-- An arbitrary matrix, if it is a bond matrix. -/
def ofMatrix? (A : Matrix (Fin n) (Fin n) ℚ) : Option (BondMatrix n) :=
  if h : IsBondMatrix A then some ⟨A, h⟩ else none

theorem ofMatrix?_eq_some_iff {A : Matrix (Fin n) (Fin n) ℚ} {B : BondMatrix n} :
    ofMatrix? A = some B ↔ B.1 = A := by
  unfold ofMatrix?
  split_ifs with h
  · constructor
    · intro e
      rw [← Option.some.inj e]
    · intro e
      exact congrArg some (Subtype.ext e.symm)
  · constructor
    · intro e
      cases e
    · intro e
      exact absurd (e ▸ B.2) h

instance : Repr (BondMatrix n) := ⟨fun B p => reprPrec B.1 p⟩

end BondMatrix

/-! ### The flat 0/1 matrix -/

/-- A 0/1 adjacency matrix — Mathlib's `Matrix.IsAdjMatrix`: symmetric, zero on
the diagonal, entries 0 or 1.  Remembers adjacency only. -/
def FlatMatrix (n : ℕ) := {A : Matrix (Fin n) (Fin n) ℚ // A.IsAdjMatrix}

namespace FlatMatrix

variable {n : ℕ}

instance : CoeFun (FlatMatrix n) (fun _ => Fin n → Fin n → ℚ) := ⟨fun F => F.1⟩

theorem ext {F F' : FlatMatrix n} (h : ∀ i j, F i j = F' i j) : F = F' :=
  Subtype.ext (Matrix.ext h)

/-- The graph, by Mathlib's `IsAdjMatrix.toGraph` (reducible, so Mathlib's
decidability instance for `toGraph` applies). -/
abbrev graph (F : FlatMatrix n) : SimpleGraph (Fin n) := F.2.toGraph

/-- Round trip, Mathlib's: the matrix of the graph of `F` is `F`. -/
theorem adjMatrix_graph (F : FlatMatrix n) : F.graph.adjMatrix ℚ = F.1 :=
  F.2.adjMatrix_toGraph_eq

instance : Repr (FlatMatrix n) := ⟨fun F p => reprPrec F.1 p⟩

end FlatMatrix

/-- Forget the bond orders: the indicator of the nonzero entries. -/
def BondMatrix.flatten (B : BondMatrix n) : FlatMatrix n :=
  ⟨B.1.map fun q => if q = 0 then 0 else 1,
    { zero_or_one := fun i j => by
        simp only [Matrix.map_apply]
        split_ifs <;> simp
      symm := by
        apply Matrix.IsSymm.ext
        intro i j
        simp only [Matrix.map_apply, B.symm i j]
      apply_diag := fun i => by simp [Matrix.map_apply, B.diag i] }⟩

theorem BondMatrix.flatten_apply (B : BondMatrix n) (i j : Fin n) :
    B.flatten i j = if B i j = 0 then 0 else 1 := rfl

/-- Flattening keeps the graph. -/
theorem BondMatrix.graph_flatten (B : BondMatrix n) : B.flatten.graph = B.graph := by
  ext i j
  change B.flatten i j = 1 ↔ (graphOfMatrix B.1).Adj i j
  rw [flatten_apply, graphOfMatrix_adj]
  constructor
  · intro h
    have hne : B i j ≠ 0 := by
      intro h0
      rw [if_pos h0] at h
      exact zero_ne_one h
    refine ⟨fun hij => hne (hij ▸ B.diag i), Or.inl hne⟩
  · rintro ⟨-, h | h⟩
    · rw [if_neg h]
    · rw [if_neg (B.symm i j ▸ h)]

namespace Molecule

variable {n : ℕ} (m : Molecule n)

/-! ### From a molecule, with O(1) lookups -/

/-- The weighted adjacency matrix as a table. -/
def adjTable : Vector (Vector ℚ n) n :=
  Vector.ofFn fun i => Vector.ofFn fun j => m.adjMatrix i j

@[simp] theorem adjTable_get (i j : Fin n) : m.adjTable[i.val][j.val] = m.adjMatrix i j := by
  simp [adjTable]

theorem of_adjTable_eq : (Matrix.of fun i j => m.adjTable[i][j]) = m.adjMatrix := by
  ext i j
  rw [Matrix.of_apply]
  exact m.adjTable_get i j

/-- The molecule's bond matrix, backed by `adjTable` so that `B i j` is O(1). -/
def toBondMatrix : BondMatrix n :=
  let t := m.adjTable
  ⟨Matrix.of fun i j => t[i][j], m.of_adjTable_eq ▸ m.adjMatrix_isBondMatrix⟩

@[simp] theorem toBondMatrix_val : m.toBondMatrix.1 = m.adjMatrix := m.of_adjTable_eq

theorem toBondMatrix_apply (i j : Fin n) : m.toBondMatrix i j = m.adjMatrix i j :=
  congrFun (congrFun m.toBondMatrix_val i) j

@[simp] theorem graph_toBondMatrix : m.toBondMatrix.graph = m.graph := by
  unfold BondMatrix.graph
  rw [toBondMatrix_val, graphOfMatrix_adjMatrix]

theorem kindAt_toBondMatrix (i j : Fin n) :
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

@[simp] theorem graph_toFlatMatrix : m.toFlatMatrix.graph = m.graph := m.toGraph_adjMatrix

/-! ### Normal form: a molecule that is nothing but atoms and a bond matrix -/

/-- Forget bond orientation and bond-list order: decode the molecule's own
matrix. -/
def normalize : Molecule n := ofAdjMatrix m.atoms m.adjMatrix

/-- Already in normal form. -/
def IsNormal : Prop := m.normalize = m

theorem ext {m m' : Molecule n} (ha : m.atoms = m'.atoms) (hb : m.bonds = m'.bonds) : m = m' := by
  cases m
  cases m'
  cases ha
  cases hb
  rfl

instance : DecidableEq (Molecule n) := fun m m' =>
  decidable_of_iff (m.atoms = m'.atoms ∧ m.bonds = m'.bonds)
    ⟨fun ⟨h1, h2⟩ => ext h1 h2, fun h => h ▸ ⟨rfl, rfl⟩⟩

instance : DecidablePred (IsNormal (n := n)) := fun m =>
  inferInstanceAs (Decidable (m.normalize = m))

@[simp] theorem atoms_normalize : m.normalize.atoms = m.atoms := rfl

@[simp] theorem adjMatrix_normalize : m.normalize.adjMatrix = m.adjMatrix :=
  m.adjMatrix_ofAdjMatrix_adjMatrix

@[simp] theorem graph_normalize : m.normalize.graph = m.graph :=
  m.graph_ofAdjMatrix_adjMatrix

theorem normalize_normalize : m.normalize.normalize = m.normalize := by
  unfold normalize
  rw [atoms_ofAdjMatrix, adjMatrix_ofAdjMatrix_adjMatrix]

theorem isNormal_normalize : m.normalize.IsNormal := m.normalize_normalize

theorem isNormal_ofAdjMatrix (atoms : Vector Atom n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsBondMatrix A) : (ofAdjMatrix atoms A).IsNormal := by
  unfold IsNormal normalize
  rw [atoms_ofAdjMatrix, adjMatrix_ofAdjMatrix atoms hA]

/-- In normal form, every bond points from the smaller index to the larger
and carries no direction mark. -/
theorem IsNormal.bond_spec {m : Molecule n} (h : m.IsNormal) {b : Bond n} (hb : b ∈ m.bonds) :
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
    rw [toBondMatrix_val]
    exact m.2
  right_inv p := by
    refine Prod.ext rfl (BondMatrix.ext fun i j => ?_)
    change (p.2.toMolecule p.1).toBondMatrix.1 i j = p.2.1 i j
    rw [toBondMatrix_val]
    exact congrFun (congrFun (adjMatrix_ofAdjMatrix p.1 p.2.2) i) j

end Molecule

/-- Normal form of a bundled molecule. -/
def Mol.normalize (M : Mol) : Mol := ⟨M.n, M.mol.normalize⟩

def Mol.isNormal (M : Mol) : Bool := decide M.mol.IsNormal

end LeanSMILES
