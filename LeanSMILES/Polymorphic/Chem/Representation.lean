module

public import LeanSMILES.Polymorphic.Chem.Fingerprint
public import LeanSMILES.Polymorphic.Chem.Descriptors
public import LeanSMILES.Polymorphic.Chem.Distance

/-!
# Molecular representations

A representation turns a molecule into a fixed-length feature vector, the input of every
learning algorithm. The basic representations:

* `morgan radius nBits`: Morgan fingerprint bits;
* `adjacency k`, `distances k`, `laplacian k`, `coulomb k`: a matrix representation
  (`Matrices.lean`, `Distance.lean`), padded or truncated to `k` atoms and flattened;
* `graphInvariants`: atom and bond counts, Zagreb and Wiener indices;
* `descriptors`: six RDKit-style descriptors.

and the combinators `append` (`++`), `scale`, `clip` and `normalize`.

The guarantees in `Proofs/Pipeline.lean` need a bound `R²` on the squared norm of the
features. `Proofs/Chem/Representation.lean` proves one for every representation that has
one independently of the molecule: `n` for the `0/1` representations (`morgan`,
`adjacency`), `n c²` for `clip c r`, `1` for `normalize r`, and the sum of the bounds for
`r₁ ++ r₂`. The unbounded ones (`distances`, `coulomb`, `descriptors`, …) become bounded
under `clip` or `normalize`.
-/

@[expose] public section

namespace Chem

open Primitives

/-- A molecular representation with `n` features. -/
structure Representation (α : Type) (n : Nat) where
  featurize : Molecule → Vec α n

namespace Representation

variable {α : Type} [Scalar α] {n a b : Nat}

/-! ## Basic representations -/

/-- A bit representation: `1` for set bits, `0` otherwise. -/
def ofBits (bits : Molecule → Vector Bool n) : Representation α n :=
  ⟨fun m => (bits m).map fun b => if b then 1 else 0⟩

/-- Morgan (ECFP-style) fingerprint bits as `0/1` features (RDKit's
`GetMorganGenerator(radius, fpSize)`). -/
def morgan (radius nBits : Nat) : Representation α nBits :=
  ofBits fun m => (m.morganFingerprint radius nBits).bits

/-- A matrix representation, padded or truncated to `k` atoms and flattened row by row. -/
def ofMatrix (k : Nat) (M : (m : Molecule) → Mat α m.size m.size) :
    Representation α (k * k) :=
  ⟨fun m => flattenMat (padMat k (M m))⟩

/-- Which pairs of the first `k` atoms are bonded (`0/1` entries). -/
def adjacency (k : Nat) : Representation α (k * k) := ofMatrix k Molecule.adjacencyBits

/-- Topological distances between the first `k` atoms. -/
def distances (k : Nat) : Representation α (k * k) := ofMatrix k Molecule.distanceMatrix

/-- The Laplacian `D - A` of the first `k` atoms. -/
def laplacian (k : Nat) : Representation α (k * k) := ofMatrix k Molecule.laplacianMatrix

/-- The topological Coulomb matrix of the first `k` atoms. -/
def coulomb (k : Nat) : Representation α (k * k) := ofMatrix k Molecule.coulombMatrix

/-- Graph invariants read off the matrix representations: number of atoms, number of
bonds, first and second Zagreb indices, Wiener index. -/
def graphInvariants : Representation α 5 :=
  ⟨fun m => #v[Scalar.fromNat m.size, Scalar.fromNat m.bonds.size, m.firstZagreb,
    m.secondZagreb, m.wienerIndex]⟩

/-- Molecular weight, heavy atoms, H-bond donors, rings, rotatable bonds and minimum
degree (`Molecule.descriptors`). -/
def descriptors : Representation α 6 :=
  ⟨fun m =>
    let d := m.descriptors
    #v[d.molecularWeight.toScalar, Scalar.fromNat d.heavyAtoms, Scalar.fromNat d.hDonors,
      Scalar.fromNat d.rings, Scalar.fromNat d.rotatableBonds, Scalar.fromNat d.minDegree]⟩

/-! ## Combinators -/

/-- Both representations' features, side by side. -/
def append (r₁ : Representation α a) (r₂ : Representation α b) : Representation α (a + b) :=
  ⟨fun m => r₁.featurize m ++ r₂.featurize m⟩

instance : HAppend (Representation α a) (Representation α b) (Representation α (a + b)) :=
  ⟨append⟩

/-- Every feature multiplied by `c`. -/
def scale (c : α) (r : Representation α n) : Representation α n :=
  ⟨fun m => smul c (r.featurize m)⟩

/-- Every feature clamped to `[-c, c]`. -/
def clip (c : α) (r : Representation α n) : Representation α n :=
  ⟨fun m => (r.featurize m).map (Scalar.clamp c)⟩

/-- Features divided by their Euclidean norm (a zero vector stays zero). -/
def normalize (r : Representation α n) : Representation α n :=
  ⟨fun m =>
    let x := r.featurize m
    if normSq x ≤ 0 then x else smul (1 / norm x) x⟩

end Representation

end Chem

end
