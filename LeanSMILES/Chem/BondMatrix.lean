/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
import LeanSMILES.Chem.Bond
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric

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

namespace LeanSMILES

variable {n : ℕ}

/-- The graph whose edges are the nonzero entries of a matrix. -/
def graphOfMatrix (A : Matrix (Fin n) (Fin n) ℚ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j ↦ A i j ≠ 0

lemma graphOfMatrix_adj (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (graphOfMatrix A).Adj i j ↔ i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0) :=
  SimpleGraph.fromRel_adj _ _ _

/-! ### The weighted bond matrix -/

/-- A matrix that is the weighted adjacency matrix of *some* molecule:
symmetric, zero on the diagonal, every nonzero entry a bond order. -/
structure IsBondMatrix (A : Matrix (Fin n) (Fin n) ℚ) : Prop where
  symm : ∀ i j, A i j = A j i
  diag : ∀ i, A i i = 0
  entry : ∀ i j, A i j ≠ 0 → ∃ k : BondKind, A i j = k.order

/-- A weighted adjacency matrix that comes from a molecule. -/
def BondMatrix (n : ℕ) := {A : Matrix (Fin n) (Fin n) ℚ // IsBondMatrix A}

namespace BondMatrix

instance : CoeFun (BondMatrix n) (fun _ ↦ Fin n → Fin n → ℚ) := ⟨fun B ↦ B.1⟩

/-- The underlying matrix. -/
def toMatrix (B : BondMatrix n) : Matrix (Fin n) (Fin n) ℚ := B.1

lemma symm (B : BondMatrix n) (i j : Fin n) : B i j = B j i := B.2.symm i j

lemma diag (B : BondMatrix n) (i : Fin n) : B i i = 0 := B.2.diag i

lemma entry (B : BondMatrix n) (i j : Fin n) (h : B i j ≠ 0) :
    ∃ k : BondKind, B i j = k.order :=
  B.2.entry i j h

@[ext] lemma ext {B B' : BondMatrix n} (h : ∀ i j, B i j = B' i j) : B = B' :=
  Subtype.ext (Matrix.ext h)

/-- The bond kind between `i` and `j`, if they are bonded. -/
def kindAt (B : BondMatrix n) (i j : Fin n) : Option BondKind := BondKind.ofOrder? (B i j)

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

lemma check_iff {A : Matrix (Fin n) (Fin n) ℚ} : check A = true ↔ IsBondMatrix A := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    beq_iff_eq, Bool.or_eq_true]
  constructor
  · intro h
    refine ⟨fun i j ↦ ((h i).2 j).1, fun i ↦ (h i).1, fun i j hij ↦ ?_⟩
    rcases ((h i).2 j).2 with h0 | hs
    · exact absurd h0 hij
    · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
      exact ⟨k, BondKind.ofOrder?_eq_some hk⟩
  · intro hA i
    refine ⟨hA.diag i, fun j ↦ ⟨hA.symm i j, ?_⟩⟩
    by_cases h0 : A i j = 0
    · exact Or.inl h0
    · obtain ⟨k, hk⟩ := hA.entry i j h0
      right
      rw [hk, BondKind.ofOrder?_order]
      rfl

instance : DecidablePred (IsBondMatrix (n := n)) := fun _ ↦ decidable_of_iff _ check_iff

/-- An arbitrary matrix, if it is a bond matrix. -/
def ofMatrix? (A : Matrix (Fin n) (Fin n) ℚ) : Option (BondMatrix n) :=
  if h : IsBondMatrix A then some ⟨A, h⟩ else none

lemma ofMatrix?_eq_some_iff {A : Matrix (Fin n) (Fin n) ℚ} {B : BondMatrix n} :
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

instance : Repr (BondMatrix n) := ⟨fun B p ↦ reprPrec B.1 p⟩

instance : DecidableEq (BondMatrix n) := fun B B' ↦
  decidable_of_iff (∀ i j, B i j = B' i j) ⟨ext, fun h _ _ ↦ h ▸ rfl⟩

/-! #### Relabeling -/

/-- Relabel the atoms: entry `(σ i, σ j)` receives entry `(i, j)`. -/
def relabel (σ : Equiv.Perm (Fin n)) (B : BondMatrix n) : BondMatrix n :=
  ⟨Matrix.of fun i j ↦ B (σ.symm i) (σ.symm j),
    { symm := fun i j ↦ B.symm (σ.symm i) (σ.symm j)
      diag := fun i ↦ B.diag (σ.symm i)
      entry := fun i j h ↦ B.entry (σ.symm i) (σ.symm j) h }⟩

@[simp] lemma relabel_apply (σ : Equiv.Perm (Fin n)) (B : BondMatrix n) (i j : Fin n) :
    B.relabel σ i j = B (σ.symm i) (σ.symm j) := rfl

lemma relabel_apply_apply (σ : Equiv.Perm (Fin n)) (B : BondMatrix n) (i j : Fin n) :
    B.relabel σ (σ i) (σ j) = B i j := by
  simp

lemma relabel_relabel (σ τ : Equiv.Perm (Fin n)) (B : BondMatrix n) :
    (B.relabel σ).relabel τ = B.relabel (σ.trans τ) := by
  ext i j
  simp

end BondMatrix

/-! ### The flat 0/1 matrix -/

/-- A 0/1 adjacency matrix — Mathlib's `Matrix.IsAdjMatrix`: symmetric, zero on
the diagonal, entries 0 or 1.  Remembers adjacency only. -/
def FlatMatrix (n : ℕ) := {A : Matrix (Fin n) (Fin n) ℚ // A.IsAdjMatrix}

namespace FlatMatrix

instance : CoeFun (FlatMatrix n) (fun _ ↦ Fin n → Fin n → ℚ) := ⟨fun F ↦ F.1⟩

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
    { zero_or_one := fun i j ↦ by
        simp only [Matrix.map_apply]
        split_ifs <;> simp
      symm := by
        apply Matrix.IsSymm.ext
        intro i j
        simp only [Matrix.map_apply, B.symm i j]
      apply_diag := fun i ↦ by simp [Matrix.map_apply, B.diag i] }⟩

lemma BondMatrix.flatten_apply (B : BondMatrix n) (i j : Fin n) :
    B.flatten i j = if B i j = 0 then 0 else 1 := rfl

/-- Flattening keeps the graph. -/
lemma BondMatrix.graph_flatten (B : BondMatrix n) : B.flatten.graph = B.graph := by
  ext i j
  change B.flatten i j = 1 ↔ (graphOfMatrix B.1).Adj i j
  rw [flatten_apply, graphOfMatrix_adj]
  constructor
  · intro h
    have hne : B i j ≠ 0 := by
      intro h0
      rw [if_pos h0] at h
      exact zero_ne_one h
    refine ⟨fun hij ↦ hne (hij ▸ B.diag i), Or.inl hne⟩
  · rintro ⟨-, h | h⟩
    · rw [if_neg h]
    · rw [if_neg (B.symm i j ▸ h)]

end LeanSMILES
