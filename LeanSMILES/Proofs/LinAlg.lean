module

public import LeanSMILES.Proofs.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Linear algebra over `ℝ`

Lemmas about the vector and matrix operations of `Polymorphic/LinAlg.lean` at `α := ℝ`:
inner products and norms (with Cauchy–Schwarz), augmented and concatenated vectors,
matrix–vector products, sparse products, and Laplacians.
-/

public section

namespace Primitives

/-! ## Inner products and norms -/

theorem dot_comm {n : ℕ} (u v : Vec ℝ n) : dot u v = dot v u := by
  simp only [dot_eq_sum, mul_comm]

theorem dot_vadd_smul {n : ℕ} (u θ d : Vec ℝ n) (t : ℝ) :
    dot u (vadd θ (smul t d)) = dot u θ + t * dot u d := by
  simp only [dot_eq_sum, vadd, smul, Fin.getElem_fin, Vector.getElem_ofFn, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem normSq_eq_sum {n : ℕ} (v : Vec ℝ n) : normSq v = ∑ i : Fin n, v[i] ^ 2 := by
  simp only [normSq, dot_eq_sum, sq]

theorem normSq_nonneg {n : ℕ} (v : Vec ℝ n) : 0 ≤ normSq v := by
  rw [normSq_eq_sum]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem normSq_vadd_smul {n : ℕ} (θ d : Vec ℝ n) (t : ℝ) :
    normSq (vadd θ (smul t d)) = normSq θ + 2 * t * dot θ d + t ^ 2 * normSq d := by
  simp only [normSq, dot_eq_sum, vadd, smul, Fin.getElem_fin, Vector.getElem_ofFn, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Cauchy–Schwarz: `⟪u, v⟫² ≤ ‖u‖² ‖v‖²`. -/
theorem dot_sq_le {n : ℕ} (u v : Vec ℝ n) : dot u v ^ 2 ≤ normSq u * normSq v := by
  rw [dot_eq_sum, normSq_eq_sum, normSq_eq_sum]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ (fun i => u[i]) (fun i => v[i])

/-- Exchange the order of a double sum `∑ⱼ (c ∑ᵢ Aᵢⱼ rᵢ) dⱼ = c ∑ᵢ rᵢ ⟪Aᵢ, d⟫`. -/
theorem sum_weighted_rows {m k : ℕ} (A : Fin m → Vec ℝ k) (r : Fin m → ℝ) (c : ℝ)
    (d : Vec ℝ k) :
    ∑ j : Fin k, (c * ∑ i : Fin m, (A i)[j] * r i) * d[j] =
      c * ∑ i : Fin m, r i * dot (A i) d := by
  simp only [dot_eq_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem normSq_smul {n : ℕ} (c : ℝ) (v : Vec ℝ n) : normSq (smul c v) = c ^ 2 * normSq v := by
  simp only [normSq_eq_sum, smul, Fin.getElem_fin, Vector.getElem_ofFn, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_vsub {n : ℕ} (w u v : Vec ℝ n) : dot w (vsub u v) = dot w u - dot w v := by
  simp only [dot_eq_sum, vsub, Fin.getElem_fin, Vector.getElem_ofFn, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem distSq_eq_sum {n : ℕ} (u v : Vec ℝ n) : distSq u v = ∑ i : Fin n, (u[i] - v[i]) ^ 2 := by
  simp [distSq, normSq_eq_sum, vsub]

/-- `‖v‖² ≤ n c` when every squared entry is at most `c`. -/
theorem normSq_le_of_sq_le {n : ℕ} (v : Vec ℝ n) {c : ℝ} (h : ∀ i : Fin n, v[i] ^ 2 ≤ c) :
    normSq v ≤ n * c := by
  rw [normSq_eq_sum]
  calc ∑ i : Fin n, v[i] ^ 2 ≤ ∑ _i : Fin n, c := Finset.sum_le_sum fun i _ => h i
    _ = n * c := by simp

/-- `‖v‖² ≤ n` for a vector of `0`s and `1`s. -/
theorem normSq_le_of_binary {n : ℕ} (v : Vec ℝ n) (h : ∀ i : Fin n, v[i] = 0 ∨ v[i] = 1) :
    normSq v ≤ n := by
  have := normSq_le_of_sq_le v (c := 1) fun i => by rcases h i with h | h <;> simp [h]
  simpa using this

/-! ## Augmented and concatenated vectors -/

@[simp] theorem augment_getElem_lt {α : Type} [Scalar α] {n : ℕ} (x : Vec α n) (j : ℕ)
    (h : j < n + 1) (hj : j < n) : (augment x)[j] = x[j] := by
  simp [augment, hj]

@[simp] theorem augment_getElem_last {α : Type} [Scalar α] {n : ℕ} (x : Vec α n)
    (h : n < n + 1) : (augment x)[n] = 1 := by
  simp [augment]

@[simp] theorem augmentMat_getElem {α : Type} [Scalar α] {m n : ℕ} (X : Mat α m n)
    (i : ℕ) (h : i < m) : (augmentMat X)[i] = augment X[i] := by
  simp [augmentMat]

/-- Appending the constant feature `1` adds `1` to the squared norm. -/
theorem normSq_augment {n : ℕ} (x : Vec ℝ n) : normSq (augment x) = normSq x + 1 := by
  rw [normSq_eq_sum, normSq_eq_sum, Fin.sum_univ_castSucc]
  simp

theorem normSq_append {a b : ℕ} (u : Vec ℝ a) (v : Vec ℝ b) :
    normSq (u ++ v) = normSq u + normSq v := by
  rw [normSq_eq_sum, normSq_eq_sum, normSq_eq_sum, Fin.sum_univ_add]
  simp

/-! ## Matrices -/

theorem matVec_vsub {m k : ℕ} (A : Mat ℝ m k) (u w : Vec ℝ k) :
    matVec A (vsub u w) = vsub (matVec A u) (matVec A w) := by
  ext i hi
  simp only [matVec, vsub, Fin.getElem_fin, Vector.getElem_ofFn, dot_eq_sum, mul_sub,
    Finset.sum_sub_distrib]

theorem matVec_gram {m k : ℕ} (A : Mat ℝ m k) (v : Vec ℝ k) :
    matVec (gram A) v = matVec (transpose A) (matVec A v) := by
  ext j hj
  simp only [gram, matMul, matVec, transpose, Fin.getElem_fin, Vector.getElem_ofFn, dot_eq_sum,
    sumFin_eq_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

@[simp] theorem diagonal_getElem {n : ℕ} (d : Vec ℝ n) (i j : ℕ) (hi : i < n) (hj : j < n) :
    (diagonal d)[i][j] = if i = j then d[i] else 0 := by
  simp [diagonal, Fin.ext_iff]

@[simp] theorem rowSums_getElem {m n : ℕ} (A : Mat ℝ m n) (i : ℕ) (hi : i < m) :
    (rowSums A)[i] = ∑ j : Fin n, A[i][j] := by
  simp [rowSums, vsum_eq_sum]

theorem laplacianOf_getElem {n : ℕ} (W : Mat ℝ n n) (i j : ℕ) (hi : i < n) (hj : j < n) :
    (laplacianOf W)[i][j] = (if i = j then ∑ k : Fin n, W[i][k] else 0) - W[i][j] := by
  simp [laplacianOf, msub]

theorem laplacianOf_symm {n : ℕ} (W : Mat ℝ n n) (hW : ∀ i j : Fin n, W[i][j] = W[j][i])
    (i j : Fin n) : (laplacianOf W)[i][j] = (laplacianOf W)[j][i] := by
  simp only [Fin.getElem_fin, laplacianOf_getElem]
  by_cases h : (i : ℕ) = j
  · simp [h]
  · simp only [h, if_false, show ¬ (j : ℕ) = i from fun h' => h h'.symm]
    simpa using congrArg Neg.neg (hW i j)

/-- Every row of a Laplacian sums to zero: `L 𝟙 = 0`. -/
theorem matVec_laplacianOf_vones {n : ℕ} (W : Mat ℝ n n) (i : Fin n) :
    (matVec (laplacianOf W) vones)[i] = 0 := by
  simp only [matVec, Fin.getElem_fin, Vector.getElem_ofFn, dot_eq_sum, vones, mul_one,
    laplacianOf_getElem, Finset.sum_sub_distrib, Fin.val_inj, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, sub_self]

/-- `⟪u, Aᵀ v⟫ = ⟪A u, v⟫`. -/
theorem dot_matVec_transpose {m k : ℕ} (A : Mat ℝ m k) (u : Vec ℝ k) (v : Vec ℝ m) :
    dot u (matVec (transpose A) v) = dot (matVec A u) v := by
  simp only [dot_eq_sum, matVec, transpose, Fin.getElem_fin, Vector.getElem_ofFn, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem trace_eq_sum {n : ℕ} (A : Mat ℝ n n) : trace A = ∑ i : Fin n, A[i][i] :=
  sumFin_eq_sum _

theorem quadForm_eq_sum {n : ℕ} (A : Mat ℝ n n) (x : Vec ℝ n) :
    quadForm A x = ∑ i : Fin n, ∑ j : Fin n, A[i][j] * (x[i] * x[j]) := by
  simp only [quadForm, matVec, dot_eq_sum, Fin.getElem_fin, Vector.getElem_ofFn, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ## Sparse vectors

Over `ℝ`, a sparse product adds exactly the nonzero terms of the dense one.
-/

section Sparse

variable {m n : ℕ}

theorem isZero_iff (x : ℝ) : Scalar.isZero x = true ↔ x = 0 := by
  simp only [Scalar.isZero, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨h₁, h₂⟩ => le_antisymm h₁ h₂, fun h => ⟨h.le, h.ge⟩⟩

/-- Folding `sdot`'s step over the nonzero entries adds every term `v[j] * w[j]`. -/
theorem foldl_filterMap_ofDense (v w : Vec ℝ n) (l : List (Fin n)) (a : ℝ) :
    ((l.filterMap fun j => if Scalar.isZero v[j] then none else some (j, v[j])).foldl
      (fun acc (p : Fin n × ℝ) => acc + p.2 * w[p.1]) a) =
      a + (l.map fun j => v[j] * w[j]).sum := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih =>
    by_cases h : Scalar.isZero v[j] = true
    · simp only [List.filterMap_cons, h, ↓reduceIte, List.map_cons, List.sum_cons]
      rw [ih, (isZero_iff _).1 h]
      ring
    · simp only [List.filterMap_cons, h, Bool.false_eq_true, ↓reduceIte, List.foldl_cons,
        List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem sdot_ofDense (v w : Vec ℝ n) : sdot (SparseVec.ofDense v) w = dot v w := by
  rw [dot_eq_sum, Fin.sum_univ_def, sdot, SparseVec.ofDense, ← Array.foldl_toList,
    Array.toList_filterMap]
  have : (Array.finRange n).toList = List.finRange n :=
    List.ext_getElem (by simp) fun i _ _ => by simp
  rw [this, foldl_filterMap_ofDense, zero_add]

theorem smatVec_ofDense (A : Mat ℝ m n) (v : Vec ℝ n) :
    smatVec (SparseMat.ofDense A) v = matVec A v := by
  ext i hi
  simp [smatVec, matVec, SparseMat.ofDense, sdot_ofDense]

end Sparse

end Primitives

end
