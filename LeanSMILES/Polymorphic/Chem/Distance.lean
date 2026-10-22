module

public import LeanSMILES.Polymorphic.Chem.Matrices

/-!
# Molecules — Topological distance

The topological distance between atoms `i` and `j` is the fewest bonds on a path between
them. It is computed by breadth-first search: `ball k i` is the set of atoms at most `k`
bonds from `i`, and `distance i j` is the first `k ≤ N` with `j ∈ ball k i`, or `N + 1`
when `j` is not reachable (another fragment of a `.`-separated SMILES).

Built on it:

* `distanceMatrix`, the `N × N` matrix of topological distances;
* `wienerIndex`, half the sum of all distances (the Wiener index);
* `coulombMatrix`, a topological Coulomb matrix: `Zᵢ^2.4 / 2` on the diagonal and
  `Zᵢ Zⱼ / d(i, j)` off it, the 3D Coulomb matrix with graph distance in place of
  Euclidean distance.

Proved in `Proofs/Chem/Distance.lean`: `distance` is a metric on atoms (zero exactly on
the diagonal, symmetric, triangle inequality), bonded atoms are at distance `1`, and
`distanceMatrix` and `coulombMatrix` are symmetric.
-/

@[expose] public section

namespace Chem

open Primitives

namespace Molecule

/-- The indices of the atoms bonded to atom `i`. -/
def nbrs (m : Molecule) (i : Nat) : List Nat := (m.neighbors i).map Prod.fst

/-- One breadth-first layer: the atoms of `S` and all their neighbours. -/
def ballStep (m : Molecule) (S : List Nat) : List Nat := (S ++ S.flatMap m.nbrs).eraseDups

/-- The atoms at most `k` bonds away from atom `i`. -/
def ball (m : Molecule) (k i : Nat) : List Nat := iterate m.ballStep k [i]

/-- `[S, ballStep S, …, ballStep^K S]`, sharing the work between consecutive layers. -/
def ballsFrom (m : Molecule) (S : List Nat) : Nat → List (List Nat)
  | 0 => [S]
  | K + 1 => S :: m.ballsFrom (m.ballStep S) K

end Molecule

/-- The index of the first list that contains `j`, or the length of `Ss` if none does. -/
def firstContaining (j : Nat) : List (List Nat) → Nat
  | [] => 0
  | S :: Ss => if j ∈ S then 0 else firstContaining j Ss + 1

namespace Molecule

/-- Topological distance: the fewest bonds on a path from atom `i` to atom `j`, or
`m.size + 1` if there is no path. -/
def distance (m : Molecule) (i j : Nat) : Nat := firstContaining j (m.ballsFrom [i] m.size)

section Matrices

variable {α : Type} [Scalar α]

/-- `D[i][j]` = topological distance between atoms `i` and `j`. Each row runs one
breadth-first search. -/
@[specialize] def distanceMatrix (m : Molecule) : Mat α m.size m.size :=
  Vector.ofFn fun i =>
    let balls := m.ballsFrom [i.val] m.size
    Vector.ofFn fun j => Scalar.fromNat (firstContaining j.val balls)

/-- The Wiener index `½ ∑ᵢ ∑ⱼ d(i, j)`: the sum of distances over unordered pairs. -/
@[specialize] def wienerIndex (m : Molecule) : α :=
  let D : Mat α m.size m.size := m.distanceMatrix
  (sumFin fun (i : Fin m.size) => vsum D[i]) / Scalar.fromNat 2

/-- `Z^2.4 / 2`, the diagonal of the Coulomb matrix (`Z^2.4 = exp (2.4 log Z)`). -/
@[specialize] def coulombDiagonal (z : α) : α :=
  Scalar.exp (Scalar.fromNat 12 / Scalar.fromNat 5 * Scalar.log z) / Scalar.fromNat 2

/-- Topological Coulomb matrix: `Zᵢ^2.4 / 2` on the diagonal, `Zᵢ Zⱼ / d(i, j)` off it. -/
@[specialize] def coulombMatrix (m : Molecule) : Mat α m.size m.size :=
  let Z : Vec α m.size := m.atomicNumbers
  let D : Mat α m.size m.size := m.distanceMatrix
  Vector.ofFn fun i => Vector.ofFn fun j =>
    if i = j then coulombDiagonal Z[i] else Z[i] * Z[j] / D[i][j]

end Matrices

end Molecule

end Chem

end
