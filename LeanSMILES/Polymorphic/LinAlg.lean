module

public import LeanSMILES.Polymorphic.Scalar

/-!
# Linear algebra primitives

Vectors and matrices are array-backed `Vector`s. They are data, not functions, so
every operation is evaluated once. With functions `Fin n → α`, the compiler treats
`f v` as the closure `fun i => …` and recomputes it on every access, which makes
iterative algorithms exponential.

Every operation is defined with `Vector.ofFn`, so proofs rewrite entries with
`Vector.getElem_ofFn` (a `simp` lemma). To use Mathlib over `ℝ`, view a vector as
`fun i => v[i] : Fin n → ℝ`.

Sums are folds (`sumFin`) rather than `Finset.sum`, because `Float` has no
`AddCommMonoid` instance. Over `ℝ`, rewrite with `sumFin_eq_sum` from
`Proofs/Basic.lean`.
-/

@[expose] public section

namespace Primitives

/-- A length-`n` vector. -/
abbrev Vec (α : Type) (n : Nat) := Vector α n

/-- An `m × n` matrix stored as `m` rows (rows are samples, columns are features). -/
abbrev Mat (α : Type) (m n : Nat) := Vector (Vector α n) m

section LinAlg

variable {α : Type} [Scalar α] {m n p : Nat}

/-- `∑ i, f i`, computed as a left fold over `0, …, n-1`. -/
@[inline] def sumFin (f : Fin n → α) : α := Fin.foldl n (fun acc i => acc + f i) 0

@[specialize] def vsum (v : Vec α n) : α := sumFin fun (i : Fin n) => v[i]

@[specialize] def dot (u v : Vec α n) : α := sumFin fun (i : Fin n) => u[i] * v[i]

@[specialize] def vadd (u v : Vec α n) : Vec α n := Vector.ofFn fun i => u[i] + v[i]

@[specialize] def vsub (u v : Vec α n) : Vec α n := Vector.ofFn fun i => u[i] - v[i]

@[specialize] def smul (c : α) (v : Vec α n) : Vec α n := Vector.ofFn fun i => c * v[i]

@[specialize] def vzero : Vec α n := Vector.ofFn fun _ => 0

/-- The all-ones vector. -/
@[specialize] def vones : Vec α n := Vector.ofFn fun _ => 1

/-- `∑ x ∈ l, x`, computed as a left fold. -/
@[specialize] def listSum (l : List α) : α := l.foldl (· + ·) 0

/-- Squared Euclidean norm `‖v‖²`. -/
@[specialize] def normSq (v : Vec α n) : α := dot v v

@[specialize] def norm (v : Vec α n) : α := Scalar.sqrt (normSq v)

/-- Squared Euclidean distance `‖u - v‖²`. -/
@[specialize] def distSq (u v : Vec α n) : α := normSq (vsub u v)

@[specialize] def transpose (A : Mat α m n) : Mat α n m :=
  Vector.ofFn fun j => Vector.ofFn fun i => A[i][j]

/-- Column `j` of `A`. -/
@[specialize] def col (A : Mat α m n) (j : Fin n) : Vec α m := Vector.ofFn fun i => A[i][j]

@[specialize] def matVec (A : Mat α m n) (v : Vec α n) : Vec α m := Vector.ofFn fun i => dot A[i] v

@[specialize] def matMul (A : Mat α m n) (B : Mat α n p) : Mat α m p :=
  Vector.ofFn fun i => Vector.ofFn fun k => sumFin fun (j : Fin n) => A[i][j] * B[j][k]

/-- Outer product `u vᵀ`. -/
@[specialize] def outer (u : Vec α m) (v : Vec α n) : Mat α m n :=
  Vector.ofFn fun i => Vector.ofFn fun j => u[i] * v[j]

def identity : Mat α n n :=
  Vector.ofFn fun i => Vector.ofFn fun j => if i = j then 1 else 0

@[specialize] def madd (A B : Mat α m n) : Mat α m n :=
  Vector.ofFn fun i => Vector.ofFn fun j => A[i][j] + B[i][j]

@[specialize] def msub (A B : Mat α m n) : Mat α m n :=
  Vector.ofFn fun i => Vector.ofFn fun j => A[i][j] - B[i][j]

@[specialize] def msmul (c : α) (A : Mat α m n) : Mat α m n :=
  Vector.ofFn fun i => Vector.ofFn fun j => c * A[i][j]

/-- The diagonal matrix with diagonal `d`. -/
@[specialize] def diagonal (d : Vec α n) : Mat α n n :=
  Vector.ofFn fun i => Vector.ofFn fun j => if i = j then d[i] else 0

@[specialize] def trace (A : Mat α n n) : α := sumFin fun (i : Fin n) => A[i][i]

/-- Row sums `A 𝟙`. -/
@[specialize] def rowSums (A : Mat α m n) : Vec α m := Vector.ofFn fun i => vsum A[i]

/-- The Laplacian `diag(W 𝟙) - W` of a weighted adjacency matrix `W`. -/
@[specialize] def laplacianOf (W : Mat α n n) : Mat α n n := msub (diagonal (rowSums W)) W

/-- The quadratic form `xᵀ A x`. -/
@[specialize] def quadForm (A : Mat α n n) (x : Vec α n) : α := dot x (matVec A x)

/-- The entries of `A`, row by row. -/
@[specialize] def flattenMat (A : Mat α m n) : Vec α (m * n) := A.flatten

/-- Column means (the centroid of the rows). -/
@[specialize] def colMean (X : Mat α m n) : Vec α n :=
  Vector.ofFn fun j => (sumFin fun (i : Fin m) => X[i][j]) / Scalar.fromNat m

/-- Subtract the column means from every row. -/
@[specialize] def center (X : Mat α m n) : Mat α m n :=
  let μ := colMean X
  Vector.ofFn fun i => vsub X[i] μ

/-- Gram matrix `XᵀX`. -/
@[specialize] def gram (X : Mat α m n) : Mat α n n := matMul (transpose X) X

/-- Append a constant `1` as the last coordinate, so an affine map `⟪w, x⟫ + b` becomes
the linear map `⟪(w, b), (x, 1)⟫`. -/
@[specialize] def augment (x : Vec α n) : Vec α (n + 1) := x.push 1

/-- `augment` applied to every row: the design matrix with a column of ones appended. -/
@[specialize] def augmentMat (X : Mat α m n) : Mat α m (n + 1) := Vector.ofFn fun i => augment X[i]

end LinAlg

/-! ## Sparse matrices

Fingerprint features are mostly zero (about 60 of 4096 bits are set), so a dense
`matVec` spends nearly all its time on `0 * x` terms. A sparse vector keeps only its
nonzero entries, in index order, and `sdot` adds exactly the terms `dot` would add, in
the same order, minus the zero ones. Over `ℝ`, `sdot (SparseVec.ofDense v) w = dot v w`
(`sdot_ofDense` in `Proofs/LinAlg.lean`).
-/

section Sparse

variable {α : Type} [Scalar α] {m n : Nat}

/-- `x = 0`, decided with the order (`Scalar` has no `DecidableEq`). -/
def Scalar.isZero (x : α) : Bool := decide (x ≤ 0) && decide (0 ≤ x)

/-- The nonzero entries `(j, v[j])` of a length-`n` vector, in increasing `j`. -/
structure SparseVec (α : Type) (n : Nat) where
  entries : Array (Fin n × α)

/-- An `m × n` sparse matrix stored as `m` sparse rows. -/
abbrev SparseMat (α : Type) (m n : Nat) := Vector (SparseVec α n) m

@[specialize] def SparseVec.ofDense (v : Vec α n) : SparseVec α n :=
  ⟨(Array.finRange n).filterMap fun j => if Scalar.isZero v[j] then none else some (j, v[j])⟩

@[specialize] def SparseMat.ofDense (A : Mat α m n) : SparseMat α m n := A.map SparseVec.ofDense

/-- `dot` of a sparse and a dense vector. -/
@[specialize] def sdot (s : SparseVec α n) (w : Vec α n) : α :=
  s.entries.foldl (fun acc (j, x) => acc + x * w[j]) 0

@[specialize] def smatVec (S : SparseMat α m n) (v : Vec α n) : Vec α m :=
  Vector.ofFn fun i => sdot S[i] v

end Sparse

/-! ## Linear systems (Gauss–Jordan elimination) -/

section LinSolve

variable {α : Type} [Scalar α] {m n p : Nat}

def swapRows (M : Mat α m p) (i j : Fin m) : Mat α m p :=
  Vector.ofFn fun r => if r = i then M[j] else if r = j then M[i] else M[r]

/-- The row `i ≥ k` with the largest `|M[i][c]|` (partial pivoting); ties go to the
smallest index. -/
def pivotRow (M : Mat α m p) (k : Fin m) (c : Fin p) : Fin m :=
  Fin.foldl m (fun best i =>
    if k ≤ i ∧ Scalar.abs M[best][c] < Scalar.abs M[i][c] then i else best) k

/-- Eliminate column `k` of the augmented system `[A | b]`: swap the pivot row into place,
then subtract multiples of it from every other row so column `k` is zero off the diagonal. -/
def gaussJordanStep (M : Mat α n (n + 1)) (k : Fin n) : Mat α n (n + 1) :=
  let M := swapRows M k (pivotRow M k k.castSucc)
  let pivot := M[k]
  Vector.ofFn fun i =>
    if i = k then pivot
    else vsub M[i] (smul (M[i][k.castSucc] / pivot[k.castSucc]) pivot)

/-- Solve `A x = b` by Gauss–Jordan elimination with partial pivoting on `[A | b]`: after
eliminating every column the left block is diagonal and `xᵢ = bᵢ' / Aᵢᵢ'`.
Proved (over `ℝ`, `linSolve_spec` in `Proofs/LinSolve.lean`): if `A` is invertible then
`matVec A (linSolve A b) = b`, and it is the only solution. If `A` is singular, a zero
pivot appears: `Float` gives `NaN`/`inf`, and `ℝ` divides by zero (`= 0`). -/
def linSolve (A : Mat α n n) (b : Vec α n) : Vec α n :=
  let M₀ : Mat α n (n + 1) :=
    Vector.ofFn fun i => A[i].push b[i]
  let M := Fin.foldl n gaussJordanStep M₀
  Vector.ofFn fun i => M[i][Fin.last n] / M[i][i.castSucc]

end LinSolve

end Primitives

end
