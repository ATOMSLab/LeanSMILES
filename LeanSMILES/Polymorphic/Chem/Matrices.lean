module

public import LeanSMILES.Polymorphic.Chem.Graph
public import LeanSMILES.Polymorphic.LinAlg

/-!
# Molecules — Matrix representations

A molecule with `N` atoms as `N × N` matrices, indexed by atom:

* `weightedAdjacency w`: `W[i][j]` is the total weight `w b` of the bonds `b` joining
  atoms `i` and `j`. Two instances:
  * `adjacencyMatrix` (`w = 1`): `A[i][j]` counts the bonds between `i` and `j`;
  * `bondOrderMatrix` (`w` = bond order, aromatic `3/2`).
* `adjacencyBits`: `1` where atoms are bonded, `0` elsewhere (bounded, so suitable as
  features; see `Representation.adjacency`).
* `degreeMatrix` `D = diag(A 𝟙)` and the Laplacians `L = diag(W 𝟙) - W`
  (`laplacianMatrix`, `bondOrderLaplacian`).
* Graph invariants read off the matrices: the Zagreb indices.

The topological distance matrix and the Coulomb matrix are in `Distance.lean`.

Proved in `Proofs/Chem/Matrices.lean`, for well-formed molecules over `ℝ`: the matrices are
symmetric with zero diagonal; the row sums of `A` are the atom degrees and sum to twice
the number of bonds (handshake lemma); `L 𝟙 = 0`; and
`xᵀ L x = ∑_bonds w_b (x_src - x_dst)²`, so every Laplacian with non-negative weights is
positive semidefinite, and its kernel is constant along every bond.
-/

@[expose] public section

namespace Chem

open Primitives

/-- Bond `b` joins atoms `i` and `j`, in either direction. -/
def Bond.joins (b : Bond) (i j : Nat) : Bool :=
  (b.src == i && b.dst == j) || (b.src == j && b.dst == i)

/-- Bond `b` has atom `i` as an end. -/
def Bond.incident (b : Bond) (i : Nat) : Bool := b.src == i || b.dst == i

/-- Bond order as a number: `1`, `2`, `3`, and `3/2` for aromatic bonds. -/
def BondOrder.weight {α : Type} [Scalar α] : BondOrder → α
  | .single => 1
  | .double => Scalar.fromNat 2
  | .triple => Scalar.fromNat 3
  | .aromatic => Scalar.fromNat 3 / Scalar.fromNat 2

namespace Molecule

/-- Number of atoms: the size of every matrix of the molecule. -/
abbrev size (m : Molecule) : Nat := m.atoms.size

/-- Number of bonds between atoms `i` and `j`. -/
def bondCount (m : Molecule) (i j : Nat) : Nat := m.bonds.toList.countP (·.joins i j)

section Matrices

variable {α : Type} [Scalar α]

/-- `W[i][j] = ∑ { w b | b joins atoms i and j }`. -/
@[specialize] def weightedAdjacency (m : Molecule) (w : Bond → α) : Mat α m.size m.size :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    listSum (m.bonds.toList.map fun b => if b.joins i j then w b else 0)

/-- `A[i][j]` = number of bonds between atoms `i` and `j`. -/
@[specialize] def adjacencyMatrix (m : Molecule) : Mat α m.size m.size :=
  m.weightedAdjacency fun _ => 1

/-- `B[i][j]` = total bond order between atoms `i` and `j`. -/
@[specialize] def bondOrderMatrix (m : Molecule) : Mat α m.size m.size :=
  m.weightedAdjacency fun b => b.order.weight

/-- `1` where atoms `i` and `j` are bonded, `0` elsewhere. -/
@[specialize] def adjacencyBits (m : Molecule) : Mat α m.size m.size :=
  Vector.ofFn fun i => Vector.ofFn fun j => if 0 < m.bondCount i j then 1 else 0

/-- The degree matrix `D = diag(A 𝟙)`. -/
@[specialize] def degreeMatrix (m : Molecule) : Mat α m.size m.size :=
  diagonal (rowSums m.adjacencyMatrix)

/-- The Laplacian `L = D - A` (Kirchhoff matrix). -/
@[specialize] def laplacianMatrix (m : Molecule) : Mat α m.size m.size :=
  laplacianOf m.adjacencyMatrix

/-- The Laplacian of the bond-order matrix. -/
@[specialize] def bondOrderLaplacian (m : Molecule) : Mat α m.size m.size :=
  laplacianOf m.bondOrderMatrix

/-- Atomic numbers, as a vector indexed by atom. -/
@[specialize] def atomicNumbers (m : Molecule) : Vec α m.size :=
  Vector.ofFn fun i => Scalar.fromNat m.atoms[i].element

/-- First Zagreb index `M₁ = ∑ᵢ deg(i)² = ‖A 𝟙‖²`. -/
@[specialize] def firstZagreb (m : Molecule) : α := normSq (rowSums (m.adjacencyMatrix (α := α)))

/-- Second Zagreb index `M₂ = ∑_bonds deg(src) · deg(dst) = ½ dᵀ A d` with `d = A 𝟙`. -/
@[specialize] def secondZagreb (m : Molecule) : α :=
  let A : Mat α m.size m.size := m.adjacencyMatrix
  quadForm A (rowSums A) / Scalar.fromNat 2

end Matrices

end Molecule

/-- The `k × k` top-left block of `A`, padded with zeros when `k > N`. Molecules have
different sizes; padding gives their matrices a common shape. -/
@[specialize] def padMat {α : Type} [Scalar α] {N : Nat} (k : Nat) (A : Mat α N N) :
    Mat α k k :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    if h : i.val < N ∧ j.val < N then (A[i.val]'h.1)[j.val]'h.2 else 0

end Chem

end
