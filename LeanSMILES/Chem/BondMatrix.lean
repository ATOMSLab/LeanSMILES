/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Chem.Bond
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# LeanSMILES.Chem.BondMatrix

Matrices that could be a molecule's, with no molecule in sight.  Two
*subtypes* of Mathlib's `Matrix`, so that "this matrix comes from a molecule"
is in the type:

* `BondMatrix n := {A : Matrix (Fin n) (Fin n) ℚ // IsBondMatrix A}` — a
  weighted adjacency matrix: symmetric, zero on the diagonal, every nonzero
  entry a bond order (aromatic `3/2`).  It remembers the bond kinds.
* `FlatMatrix n := {A : Matrix (Fin n) (Fin n) ℚ // A.IsAdjMatrix}` — a 0/1
  adjacency matrix, Mathlib's `Matrix.IsAdjMatrix`.  It remembers adjacency
  only, and is what spectral and walk-counting arguments want.

`IsBondMatrix` is decidable (`BondMatrix.check`), so `BondMatrix.ofMatrix?`
accepts or rejects an arbitrary matrix, and `graphOfMatrix` reads a simple
graph off the nonzero entries.  That a `Molecule`'s own matrix is a bond
matrix, and that a bond matrix decodes back into a molecule, is
`LeanSMILES.Chem.Graph`, which imports this file.
-/

@[expose] public section

namespace LeanSMILES

variable {n : ℕ}

/-- The graph whose edges are the nonzero entries of a matrix. -/
def graphOfMatrix (A : Matrix (Fin n) (Fin n) ℚ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j ↦ A i j ≠ 0

/-- Adjacency in `graphOfMatrix`: distinct indices with a nonzero entry in either position. -/
@[simp] lemma graphOfMatrix_adj (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (graphOfMatrix A).Adj i j ↔ i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0) :=
  SimpleGraph.fromRel_adj ..

/-! ### The weighted bond matrix -/

/-- A matrix that is the weighted adjacency matrix of *some* molecule:
symmetric, zero on the diagonal, every nonzero entry a bond order. -/
structure IsBondMatrix (A : Matrix (Fin n) (Fin n) ℚ) : Prop where
  /-- Symmetric: a bond has no direction. -/
  symm : ∀ i j, A i j = A j i
  /-- Zero diagonal: no atom is bonded to itself. -/
  diag : ∀ i, A i i = 0
  /-- Every nonzero entry is the order of some bond kind. -/
  entry : ∀ i j, A i j ≠ 0 → ∃ k : BondKind, A i j = k.order

/-- A weighted adjacency matrix that comes from a molecule. -/
def BondMatrix (n : ℕ) := {A : Matrix (Fin n) (Fin n) ℚ // IsBondMatrix A}

namespace BondMatrix

instance : CoeFun (BondMatrix n) (fun _ ↦ Fin n → Fin n → ℚ) := ⟨fun B ↦ B.1⟩

/-- The underlying matrix. -/
def toMatrix (B : BondMatrix n) : Matrix (Fin n) (Fin n) ℚ := B.1

/-- Bond matrices are symmetric: a bond has no direction. -/
lemma symm (B : BondMatrix n) (i j : Fin n) : B i j = B j i := B.2.symm i j

/-- Bond matrices have zero diagonal: no atom is bonded to itself. -/
@[simp] lemma diag (B : BondMatrix n) (i : Fin n) : B i i = 0 := B.2.diag i

/-- Every nonzero entry of a bond matrix is the order of some bond kind. -/
lemma entry (B : BondMatrix n) (i j : Fin n) (h : B i j ≠ 0) : ∃ k : BondKind, B i j = k.order :=
  B.2.entry i j h

/-- Bond matrices with the same entries are equal; tagged `@[ext]`, so `ext i j` reduces an
equality of bond matrices to one of entries. -/
@[ext] lemma ext {B B' : BondMatrix n} (h : ∀ i j, B i j = B' i j) : B = B' :=
  Subtype.ext (Matrix.ext h)

/-- The bond kind between `i` and `j`, if they are bonded. -/
def kindAt (B : BondMatrix n) (i j : Fin n) : Option BondKind := BondKind.ofOrder? (B i j)

/-- `kindAt` returns `k` exactly when the entry is `k`'s order: the way to reason about `kindAt`
without unfolding it. -/
lemma kindAt_eq_some_iff {B : BondMatrix n} {i j : Fin n} {k : BondKind} :
    B.kindAt i j = some k ↔ B i j = k.order :=
  ⟨BondKind.ofOrder?_eq_some, fun h ↦ by rw [kindAt, h, BondKind.ofOrder?_order]⟩

/-- The graph of the nonzero entries. -/
def graph (B : BondMatrix n) : SimpleGraph (Fin n) := graphOfMatrix B.1

/-! #### Checking an arbitrary matrix -/

/-- Executable test for `IsBondMatrix`. -/
def check (A : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  (List.finRange n).all fun i ↦
    A i i == 0 && (List.finRange n).all fun j ↦
      A i j == A j i && (A i j == 0 || (BondKind.ofOrder? (A i j)).isSome)

/-- `check` decides `IsBondMatrix`: the executable test is sound and complete, which is what
makes `IsBondMatrix` decidable and `ofMatrix?` computable. -/
lemma check_iff {A : Matrix (Fin n) (Fin n) ℚ} : check A = true ↔ IsBondMatrix A := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    beq_iff_eq, Bool.or_eq_true, Option.isSome_iff_exists]
  refine ⟨fun h ↦ ⟨fun i j ↦ ((h i).2 j).1, fun i ↦ (h i).1, fun i j hij ↦
    (((h i).2 j).2.resolve_left hij).imp fun _ ↦ BondKind.ofOrder?_eq_some⟩, fun hA i ↦ ?_⟩
  grind [hA.symm, hA.diag, hA.entry, BondKind.ofOrder?_order]

instance : DecidablePred (IsBondMatrix (n := n)) := fun _ ↦ decidable_of_iff _ check_iff

/-- An arbitrary matrix, if it is a bond matrix. -/
def ofMatrix? (A : Matrix (Fin n) (Fin n) ℚ) : Option (BondMatrix n) :=
  if h : IsBondMatrix A then some ⟨A, h⟩ else none

/-- `ofMatrix?` returns `some B` exactly when `A` is `B`'s matrix: decoding succeeds precisely on
bond matrices and returns the matrix unchanged. -/
lemma ofMatrix?_eq_some_iff {A : Matrix (Fin n) (Fin n) ℚ} {B : BondMatrix n} :
    ofMatrix? A = some B ↔ B.1 = A := by
  simp only [ofMatrix?, Option.dite_none_right_eq_some, Option.some.injEq]
  exact ⟨fun ⟨_, e⟩ ↦ congrArg Subtype.val e.symm, fun e ↦ ⟨e ▸ B.2, Subtype.ext e.symm⟩⟩

instance : Repr (BondMatrix n) := ⟨fun B p ↦ reprPrec B.1 p⟩

instance : DecidableEq (BondMatrix n) := fun B B' ↦
  decidable_of_iff (∀ i j, B i j = B' i j) BondMatrix.ext_iff.symm

/-! #### Relabeling -/

/-- Relabel the atoms: entry `(σ i, σ j)` receives entry `(i, j)`. -/
def relabel (σ : Equiv.Perm (Fin n)) (B : BondMatrix n) : BondMatrix n :=
  ⟨Matrix.of fun i j ↦ B (σ.symm i) (σ.symm j),
    { symm := fun i j ↦ B.symm (σ.symm i) (σ.symm j)
      diag := fun i ↦ B.diag (σ.symm i)
      entry := fun i j h ↦ B.entry (σ.symm i) (σ.symm j) h }⟩

/-- Entry `(i, j)` of the relabeled matrix is entry `(σ⁻¹ i, σ⁻¹ j)` of the original. -/
@[simp] lemma relabel_apply (σ : Equiv.Perm (Fin n)) (B : BondMatrix n) (i j : Fin n) :
    B.relabel σ i j = B (σ.symm i) (σ.symm j) := rfl

/-- `relabel_apply` read forwards: the relabeled matrix at `(σ i, σ j)` is the original at
`(i, j)`. -/
lemma relabel_apply_apply (σ : Equiv.Perm (Fin n)) (B : BondMatrix n) (i j : Fin n) :
    B.relabel σ (σ i) (σ j) = B i j := by simp

/-- Two relabelings in a row are one relabeling along the composite. -/
@[simp] lemma relabel_relabel (σ τ : Equiv.Perm (Fin n)) (B : BondMatrix n) :
    (B.relabel σ).relabel τ = B.relabel (σ.trans τ) :=
  ext fun _ _ ↦ by simp

end BondMatrix

/-! ### The flat 0/1 matrix -/

/-- A 0/1 adjacency matrix — Mathlib's `Matrix.IsAdjMatrix`: symmetric, zero on
the diagonal, entries 0 or 1.  Remembers adjacency only. -/
def FlatMatrix (n : ℕ) := {A : Matrix (Fin n) (Fin n) ℚ // A.IsAdjMatrix}

namespace FlatMatrix

instance : CoeFun (FlatMatrix n) (fun _ ↦ Fin n → Fin n → ℚ) := ⟨fun F ↦ F.1⟩

/-- Flat matrices with the same entries are equal; tagged `@[ext]`, so `ext i j` reduces an
equality of flat matrices to one of entries. -/
@[ext] lemma ext {F F' : FlatMatrix n} (h : ∀ i j, F i j = F' i j) : F = F' :=
  Subtype.ext (Matrix.ext h)

/-- The graph, by Mathlib's `IsAdjMatrix.toGraph` (reducible, so Mathlib's
decidability instance for `toGraph` applies). -/
abbrev graph (F : FlatMatrix n) : SimpleGraph (Fin n) := F.2.toGraph

/-- Round trip, Mathlib's: the matrix of the graph of `F` is `F`. -/
lemma adjMatrix_graph (F : FlatMatrix n) : F.graph.adjMatrix ℚ = F.1 :=
  F.2.adjMatrix_toGraph_eq

instance : Repr (FlatMatrix n) := ⟨fun F p ↦ reprPrec F.1 p⟩

end FlatMatrix

/-- Forget the bond orders: the indicator of the nonzero entries. -/
def BondMatrix.flatten (B : BondMatrix n) : FlatMatrix n :=
  ⟨B.1.map fun q ↦ if q = 0 then 0 else 1,
    { zero_or_one := fun i j ↦ by grind [Matrix.map_apply]
      symm := (Matrix.IsSymm.ext fun i j ↦ B.symm j i).map _
      apply_diag := fun i ↦ by simp }⟩

/-- Entry `(i, j)` of the flattened matrix: `1` if `B i j ≠ 0`, else `0`. -/
@[simp] lemma BondMatrix.flatten_apply (B : BondMatrix n) (i j : Fin n) :
    B.flatten i j = if B i j = 0 then 0 else 1 := rfl

/-- Flattening keeps the graph. -/
@[simp] lemma BondMatrix.graph_flatten (B : BondMatrix n) : B.flatten.graph = B.graph := by
  ext i j
  grind [Matrix.IsAdjMatrix.toGraph_adj, flatten_apply, BondMatrix.graph, graphOfMatrix_adj,
    B.diag, B.symm]

end LeanSMILES
