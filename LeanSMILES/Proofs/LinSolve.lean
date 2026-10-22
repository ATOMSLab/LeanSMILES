module

public import LeanSMILES.Proofs.LinAlg
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Gauss–Jordan elimination is correct

`linSolve A b` (`Polymorphic/LinAlg.lean`) runs Gauss–Jordan elimination with partial
pivoting on the augmented matrix `[A | b]`. Over `ℝ`:

* **`linSolve_spec`**: if `A` has full column rank (`A x = 0 → x = 0`, i.e. `A` is
  invertible), then `A (linSolve A b) = b`; `linSolve_spec_of_det_ne_zero` states it with
  `det A ≠ 0`.
* **`linSolve_unique`**: it is then the only solution.

The proof follows the algorithm. Call `y : ℝⁿ⁺¹` a *null vector* of an augmented matrix
`M` when every row has `⟪M[i], y⟫ = 0` (`Kills`); `A x = b` says exactly that `(x, -1)`
is a null vector of `[A | b]`.

1. Swapping rows and subtracting multiples of the pivot row from the other rows are
   invertible row operations, so every step keeps the null vectors, whatever the pivot
   (`kills_gaussJordanStep`).
2. After `k` steps, columns `0, …, k-1` are zero off the diagonal, with non-zero diagonal
   entries (`Reduced`). The step for column `k` keeps this and adds column `k`, provided
   the pivot is non-zero (`reduced_gaussJordanStep`).
3. The pivot is the largest `|M[i][k]|` over `i ≥ k` (`pivotRow_spec`). If it were `0`,
   column `k` would vanish below the diagonal, and the vector
   `yₖ = 1, yⱼ = -M[j][k] / M[j][j] (j < k)` would be a null vector with last entry `0`,
   giving a non-zero `x` with `A x = 0` (`exists_pivot_ne_zero`).
4. After `n` steps the left block is diagonal, so `xᵢ = M[i][n] / M[i][i]` (what
   `linSolve` returns) makes `(x, -1)` a null vector of the final matrix, hence of
   `[A | b]`.

As a consequence, OLS is optimal whenever the augmented features are linearly
independent (`solvesNormalEquations_of_fullColumnRank` in `Proofs/ML/LeastSquares.lean`):
a condition on the data alone.
-/

public section

namespace Primitives

open Finset

@[simp] theorem Scalar.abs_real (x : ℝ) : Scalar.abs x = |x| := rfl

/-- `A x = 0` only for `x = 0`: the columns of `A` are linearly independent. For a square
matrix, this is invertibility. -/
@[expose] def FullColumnRank {m n : ℕ} (A : Mat ℝ m n) : Prop :=
  ∀ x : Vec ℝ n, matVec A x = vzero → x = vzero

/-! ## Row operations keep the null vectors -/

section RowOps

variable {n : ℕ}

/-- Every row of `M` is orthogonal to `y`: `y` solves the homogeneous system `M y = 0`. -/
def Kills {m p : ℕ} (M : Mat ℝ m p) (y : Vec ℝ p) : Prop := ∀ i : Fin m, dot M[i] y = 0

theorem swapRows_getElem {α : Type} [Scalar α] {m p : ℕ} (M : Mat α m p) (a b r : Fin m) :
    (swapRows M a b)[r] = if r = a then M[b] else if r = b then M[a] else M[r] := by
  simp [swapRows]

theorem kills_swapRows {m p : ℕ} (M : Mat ℝ m p) (a b : Fin m) (y : Vec ℝ p) :
    Kills (swapRows M a b) y ↔ Kills M y := by
  constructor
  · intro h r
    by_cases hra : r = a
    · have := h b
      rw [swapRows_getElem] at this
      subst hra
      by_cases hba : b = r
      · subst hba; simpa using this
      · simpa [hba] using this
    · by_cases hrb : r = b
      · have := h a
        rw [swapRows_getElem] at this
        simpa [hrb] using this
      · have := h r
        rwa [swapRows_getElem, if_neg hra, if_neg hrb] at this
  · intro h r
    rw [swapRows_getElem]
    split_ifs
    · exact h b
    · exact h a
    · exact h r

theorem dot_vsub_smul {p : ℕ} (u v y : Vec ℝ p) (c : ℝ) :
    dot (vsub u (smul c v)) y = dot u y - c * dot v y := by
  simp only [dot_eq_sum, vsub, smul, Fin.getElem_fin, Vector.getElem_ofFn, mul_sum,
    ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- Subtracting multiples of row `k` from the other rows keeps the null vectors. -/
theorem kills_elim {p : ℕ} (S : Mat ℝ n p) (k : Fin n) (c : Fin n → ℝ) (y : Vec ℝ p) :
    Kills (Vector.ofFn fun i => if i = k then S[k] else vsub S[i] (smul (c i) S[k])) y ↔
      Kills S y := by
  constructor
  · intro h i
    have hk := h k
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, if_true] at hk
    by_cases hik : i = k
    · subst hik; exact hk
    · have hi := h i
      simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, if_neg hik,
        dot_vsub_smul] at hi
      simp only [Fin.getElem_fin] at hk ⊢
      rw [hk, mul_zero, sub_zero] at hi
      exact hi
  · intro h i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
    split_ifs with hik
    · exact h k
    · rw [dot_vsub_smul]
      have hi := h i
      have hk := h k
      simp only [Fin.getElem_fin] at hi hk
      rw [hi, hk, mul_zero, sub_zero]

theorem gaussJordanStep_eq (M : Mat ℝ n (n + 1)) (k : Fin n) :
    gaussJordanStep M k =
      let S := swapRows M k (pivotRow M k k.castSucc)
      Vector.ofFn fun i =>
        if i = k then S[k] else vsub S[i] (smul (S[i][k.castSucc] / S[k][k.castSucc]) S[k]) :=
  rfl

/-- **Each elimination step keeps the null vectors**, whatever the pivot. -/
theorem kills_gaussJordanStep (M : Mat ℝ n (n + 1)) (k : Fin n) (y : Vec ℝ (n + 1)) :
    Kills (gaussJordanStep M k) y ↔ Kills M y := by
  rw [gaussJordanStep_eq]
  exact (kills_elim _ k _ y).trans (kills_swapRows M _ _ y)

end RowOps

/-! ## Partial pivoting -/

section Pivot

variable {m p : ℕ}

theorem pivot_foldl (M : Mat ℝ m p) (k : Fin m) (c : Fin p) (f : Fin m → Fin m → Fin m)
    (hf : ∀ best i, f best i =
      if k ≤ i ∧ Scalar.abs M[best][c] < Scalar.abs M[i][c] then i else best)
    (l : List (Fin m)) (best : Fin m) (hb : k ≤ best) :
    k ≤ l.foldl f best ∧ |M[best][c]| ≤ |M[l.foldl f best][c]| ∧
      ∀ i ∈ l, k ≤ i → |M[i][c]| ≤ |M[l.foldl f best][c]| := by
  induction l generalizing best with
  | nil => simp [hb]
  | cons i l ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    by_cases h : k ≤ i ∧ Scalar.abs M[best][c] < Scalar.abs M[i][c]
    · have hfi : f best i = i := by rw [hf, if_pos h]
      simp only [hfi]
      obtain ⟨h1, h2, h3⟩ := ih i h.1
      simp only [Scalar.abs_real] at h
      exact ⟨h1, (le_of_lt h.2).trans h2, fun _ => h2, h3⟩
    · have hfi : f best i = best := by rw [hf, if_neg h]
      simp only [hfi]
      obtain ⟨h1, h2, h3⟩ := ih best hb
      refine ⟨h1, h2, fun hi => ?_, h3⟩
      simp only [Scalar.abs_real, not_and, not_lt] at h
      exact (h hi).trans h2

/-- The pivot row is at or below row `k`, and has the largest `|M[i][c]|` among the rows
`i ≥ k`. -/
theorem pivotRow_spec (M : Mat ℝ m p) (k : Fin m) (c : Fin p) :
    k ≤ pivotRow M k c ∧ ∀ i : Fin m, k ≤ i → |M[i][c]| ≤ |M[pivotRow M k c][c]| := by
  have hdef : pivotRow M k c = Fin.foldl m (fun best i =>
      if k ≤ i ∧ Scalar.abs M[best][c] < Scalar.abs M[i][c] then i else best) k := rfl
  obtain ⟨h1, -, h3⟩ := pivot_foldl M k c _ (fun _ _ => rfl) (List.finRange m) k le_rfl
  simp only [hdef, Fin.foldl_eq_finRange_foldl]
  exact ⟨h1, fun i hi => h3 i (List.mem_finRange i) hi⟩

end Pivot

/-! ## The reduced form -/

section Reduced

variable {n : ℕ}

/-- Columns `0, …, k-1` of `M` are zero off the diagonal and non-zero on it. -/
def Reduced (M : Mat ℝ n (n + 1)) (k : ℕ) : Prop :=
  ∀ j : Fin n, (j : ℕ) < k → M[j][j.castSucc] ≠ 0 ∧ ∀ i : Fin n, i ≠ j → M[i][j.castSucc] = 0

/-- The vector certifying that column `k` depends on columns `0, …, k-1`. -/
noncomputable def nullCandidate (M : Mat ℝ n (n + 1)) (k : Fin n) : Vec ℝ (n + 1) :=
  Vector.ofFn fun j =>
    if j = k.castSucc then 1
    else if h : (j : ℕ) < k then
      -M[(⟨j, by omega⟩ : Fin n)][k.castSucc] /
        M[(⟨j, by omega⟩ : Fin n)][(⟨j, by omega⟩ : Fin (n + 1))]
    else 0

theorem nullCandidate_k (M : Mat ℝ n (n + 1)) (k : Fin n) :
    (nullCandidate M k)[k.castSucc] = 1 := by
  simp only [nullCandidate, Fin.getElem_fin, Vector.getElem_ofFn]
  simp

theorem nullCandidate_lt (M : Mat ℝ n (n + 1)) (k j : Fin n) (hj : (j : ℕ) < k) :
    (nullCandidate M k)[j.castSucc] = -M[j][k.castSucc] / M[j][j.castSucc] := by
  simp only [nullCandidate, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [if_neg (by simp [Fin.ext_iff]; omega), dif_pos (by simpa using hj)]
  rfl

theorem nullCandidate_gt (M : Mat ℝ n (n + 1)) (k : Fin n) (j : Fin (n + 1))
    (hj : (k : ℕ) < j) : (nullCandidate M k)[j] = 0 := by
  simp only [nullCandidate, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [if_neg (by simp [Fin.ext_iff]; omega), dif_neg (by omega)]

/-- If column `k` of a reduced matrix vanishes from row `k` down, then `nullCandidate` is
a null vector. -/
theorem kills_nullCandidate (M : Mat ℝ n (n + 1)) (k : Fin n) (hred : Reduced M k)
    (hzero : ∀ i : Fin n, k ≤ i → M[i][k.castSucc] = 0) : Kills M (nullCandidate M k) := by
  intro i
  rw [dot_eq_sum]
  -- the terms `j < k`, `j ≠ i` vanish: column `j` is zero off the diagonal
  have hoff : ∀ j : Fin (n + 1), (j : ℕ) < k → j ≠ i.castSucc →
      M[i][j] * (nullCandidate M k)[j] = 0 := by
    intro j hj hji
    obtain ⟨j', rfl⟩ : ∃ j' : Fin n, j = j'.castSucc := ⟨⟨j, by omega⟩, Fin.ext rfl⟩
    rw [(hred j' hj).2 i (fun h => hji (by rw [h])), zero_mul]
  have hgt : ∀ j : Fin (n + 1), (k : ℕ) < j → M[i][j] * (nullCandidate M k)[j] = 0 :=
    fun j hj => by rw [nullCandidate_gt M k j hj, mul_zero]
  by_cases hik : (i : ℕ) < k
  · -- row `i < k`: the diagonal term cancels the column-`k` term
    rw [Fintype.sum_eq_add i.castSucc k.castSucc (by simp [Fin.ext_iff]; omega)]
    · have hii := (hred i hik).1
      rw [nullCandidate_lt M k i hik, nullCandidate_k]
      field_simp
      ring
    · intro j ⟨hj1, hj2⟩
      rcases lt_trichotomy (j : ℕ) k with hj | hj | hj
      · exact hoff j hj hj1
      · exact absurd (Fin.ext (by simpa using hj)) hj2
      · exact hgt j hj
  · -- row `i ≥ k`: every term vanishes
    refine sum_eq_zero fun j _ => ?_
    rcases lt_trichotomy (j : ℕ) k with hj | hj | hj
    · exact hoff j hj (fun h => by rw [h] at hj; simp at hj; omega)
    · have : j = k.castSucc := Fin.ext (by simpa using hj)
      rw [this, hzero i (show (k : ℕ) ≤ i by omega), zero_mul]
    · exact hgt j hj

/-- No null vector with last entry `0` other than `0` itself: the left block is
injective. -/
def LeftInjective (M : Mat ℝ n (n + 1)) : Prop :=
  ∀ y : Vec ℝ (n + 1), Kills M y → y[Fin.last n] = 0 → ∀ j : Fin (n + 1), y[j] = 0

/-- **The pivot is never zero** when the left block is injective. -/
theorem exists_pivot_ne_zero (M : Mat ℝ n (n + 1)) (k : Fin n) (hred : Reduced M k)
    (hinj : LeftInjective M) : ∃ i : Fin n, k ≤ i ∧ M[i][k.castSucc] ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hy := hinj _ (kills_nullCandidate M k hred hcon)
    (nullCandidate_gt M k (Fin.last n) (by rw [Fin.val_last]; exact k.isLt)) k.castSucc
  rw [nullCandidate_k] at hy
  exact one_ne_zero hy

theorem pivot_ne_zero (M : Mat ℝ n (n + 1)) (k : Fin n) (hred : Reduced M k)
    (hinj : LeftInjective M) : M[pivotRow M k k.castSucc][k.castSucc] ≠ 0 := by
  obtain ⟨i, hki, hi⟩ := exists_pivot_ne_zero M k hred hinj
  have := (pivotRow_spec M k k.castSucc).2 i hki
  intro h0
  rw [h0, abs_zero] at this
  exact hi (abs_nonpos_iff.mp this)

/-- **One step extends the reduced form by one column.** -/
theorem reduced_gaussJordanStep (M : Mat ℝ n (n + 1)) (k : Fin n) (hred : Reduced M k)
    (hinj : LeftInjective M) : Reduced (gaussJordanStep M k) (k + 1) := by
  set q := pivotRow M k k.castSucc with hq
  have hkq : k ≤ q := (pivotRow_spec M k k.castSucc).1
  have hpiv : M[q][k.castSucc] ≠ 0 := pivot_ne_zero M k hred hinj
  set S := swapRows M k q with hS
  have hSk : S[k] = M[q] := by rw [hS, swapRows_getElem, if_pos rfl]
  -- the swap keeps the first `k` columns reduced
  have hkq' : (k : ℕ) ≤ q := hkq
  have hSj : ∀ j : Fin n, (j : ℕ) < k → ∀ i : Fin n, S[i][j.castSucc] = M[i][j.castSucc] := by
    intro j hj i
    have hkj : k ≠ j := fun h => by rw [Fin.ext_iff] at h; omega
    have hqj : q ≠ j := fun h => by rw [Fin.ext_iff] at h; omega
    rw [hS, swapRows_getElem]
    split_ifs with h1 h2
    · rw [(hred j hj).2 q hqj, (hred j hj).2 i (by rw [h1]; exact hkj)]
    · rw [(hred j hj).2 k hkj, (hred j hj).2 i (by rw [h2]; exact hqj)]
    · rfl
  have hSkk : S[k][k.castSucc] ≠ 0 := by rw [hSk]; exact hpiv
  have hSkj : ∀ j : Fin n, (j : ℕ) < k → S[k][j.castSucc] = 0 := fun j hj => by
    rw [hSj j hj k]; exact (hred j hj).2 k (by intro h; simp [Fin.ext_iff] at h; omega)
  have hrow : ∀ i : Fin n, (gaussJordanStep M k)[i] =
      if i = k then S[k] else vsub S[i] (smul (S[i][k.castSucc] / S[k][k.castSucc]) S[k]) :=
    fun i => by rw [gaussJordanStep_eq]; simp [hS, hq]
  have hentry : ∀ (i : Fin n) (c : Fin (n + 1)), (gaussJordanStep M k)[i][c] =
      if i = k then S[k][c] else S[i][c] - S[i][k.castSucc] / S[k][k.castSucc] * S[k][c] := by
    intro i c
    rw [hrow]
    split_ifs <;> simp [vsub, smul]
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · -- an old column: unchanged, since `S[k]` vanishes there
    refine ⟨?_, fun i hij => ?_⟩
    · rw [hentry, if_neg (by intro h; simp [Fin.ext_iff] at h; omega), hSkj j hj, mul_zero,
        sub_zero, hSj j hj]
      exact (hred j hj).1
    · rw [hentry]
      split_ifs with hik
      · subst hik; exact hSkj j hj
      · rw [hSkj j hj, mul_zero, sub_zero, hSj j hj]; exact (hred j hj).2 i hij
  · -- the new column `k`
    have hjk : j = k := Fin.ext hj
    subst hjk
    refine ⟨?_, fun i hij => ?_⟩
    · rw [hentry, if_pos rfl]; exact hSkk
    · rw [hentry, if_neg hij]
      field_simp
      ring

end Reduced

/-! ## The whole elimination -/

section Elimination

variable {n : ℕ}

/-- The first `k` elimination steps. -/
noncomputable def gjPrefix (M₀ : Mat ℝ n (n + 1)) (k : ℕ) : Mat ℝ n (n + 1) :=
  ((List.finRange n).take k).foldl gaussJordanStep M₀

theorem gjPrefix_succ (M₀ : Mat ℝ n (n + 1)) (k : ℕ) (hk : k < n) :
    gjPrefix M₀ (k + 1) = gaussJordanStep (gjPrefix M₀ k) ⟨k, hk⟩ := by
  have h : (List.finRange n)[k]? = some ⟨k, hk⟩ := by
    rw [List.getElem?_eq_getElem (by simpa using hk)]
    simp
  simp [gjPrefix, List.take_add_one, h, List.foldl_append]

theorem gjPrefix_n (M₀ : Mat ℝ n (n + 1)) : gjPrefix M₀ n = Fin.foldl n gaussJordanStep M₀ := by
  rw [gjPrefix, Fin.foldl_eq_finRange_foldl, List.take_of_length_le (by simp)]

/-- **Invariant of the elimination**: after `k` steps the null vectors are unchanged and
the first `k` columns are reduced. -/
theorem gjPrefix_spec (M₀ : Mat ℝ n (n + 1)) (hinj : LeftInjective M₀) (k : ℕ) (hk : k ≤ n) :
    (∀ y, Kills (gjPrefix M₀ k) y ↔ Kills M₀ y) ∧ Reduced (gjPrefix M₀ k) k := by
  induction k with
  | zero => exact ⟨fun _ => Iff.rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨hkills, hred⟩ := ih (by omega)
    have hinj' : LeftInjective (gjPrefix M₀ k) :=
      fun y hy hlast => hinj y ((hkills y).mp hy) hlast
    rw [gjPrefix_succ M₀ k (by omega)]
    exact ⟨fun y => (kills_gaussJordanStep _ _ y).trans (hkills y),
      reduced_gaussJordanStep _ ⟨k, by omega⟩ hred hinj'⟩

end Elimination

/-! ## Correctness of `linSolve` -/

section LinSolve

variable {n : ℕ}

/-- `⟪(u, a), y⟫ = ⟪u, y₀..ₙ₋₁⟫ + a yₙ`. -/
theorem dot_push (u : Vec ℝ n) (a : ℝ) (y : Vec ℝ (n + 1)) :
    dot (u.push a) y = dot u (Vector.ofFn fun j => y[j.castSucc]) + a * y[Fin.last n] := by
  rw [dot_eq_sum, dot_eq_sum, Fin.sum_univ_castSucc]
  simp

/-- The augmented matrix `[A | b]`. -/
abbrev augmented (A : Mat ℝ n n) (b : Vec ℝ n) : Mat ℝ n (n + 1) :=
  Vector.ofFn fun i => A[i].push b[i]

theorem augmented_getElem (A : Mat ℝ n n) (b : Vec ℝ n) (i : Fin n) :
    (augmented A b)[i] = A[i].push b[i] := by
  simp [augmented]

theorem leftInjective_augmented (A : Mat ℝ n n) (b : Vec ℝ n)
    (hA : FullColumnRank A) : LeftInjective (augmented A b) := by
  intro y hy hlast j
  set x : Vec ℝ n := Vector.ofFn fun j => y[j.castSucc]
  have hx : matVec A x = vzero := by
    ext i hi
    have := hy ⟨i, hi⟩
    simp only [augmented, Fin.getElem_fin, Vector.getElem_ofFn, dot_push, hlast,
      mul_zero, add_zero] at this
    simpa [matVec, vzero] using this
  have hx0 := hA x hx
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · have := congrArg (·[j]) hx0
    simpa [x, vzero] using this
  · exact hlast

/-- **Gauss–Jordan elimination is correct.** If `A` has full rank (equivalently, is
invertible), `linSolve A b` solves `A x = b`. -/
theorem linSolve_spec (A : Mat ℝ n n) (b : Vec ℝ n)
    (hA : FullColumnRank A) : matVec A (linSolve A b) = b := by
  obtain ⟨hkills, hred⟩ :=
    gjPrefix_spec (augmented A b) (leftInjective_augmented A b hA) n le_rfl
  rw [gjPrefix_n] at hkills hred
  set M := Fin.foldl n gaussJordanStep (augmented A b) with hM
  set x : Vec ℝ n := Vector.ofFn fun i => M[i][Fin.last n] / M[i][i.castSucc]
  have hx : linSolve A b = x := rfl
  -- `(x, -1)` is a null vector of the final, diagonal system
  set y : Vec ℝ (n + 1) := x.push (-1)
  have hylast : y[Fin.last n] = -1 := by simp [y]
  have hyx : (Vector.ofFn fun j : Fin n => y[j.castSucc]) = x := by
    ext j hj
    simp [y]
  have hyM : Kills M y := by
    intro i
    rw [dot_eq_sum, Fin.sum_univ_castSucc,
      Fintype.sum_eq_single i fun j hji => by
        rw [(hred j j.isLt).2 i (Ne.symm hji)]; ring]
    have hyi : y[i.castSucc] = x[i] := by
      have := congrArg (·[i]) hyx
      simpa using this.symm.symm
    rw [hyi, hylast]
    have := (hred i i.isLt).1
    simp only [x, Fin.getElem_fin, Vector.getElem_ofFn] at this ⊢
    field_simp
    ring
  have hy0 := (hkills y).mp hyM
  rw [hx]
  ext i hi
  have h := hy0 ⟨i, hi⟩
  rw [augmented_getElem, dot_push, hyx, hylast] at h
  have hmv : (matVec A x)[i] = dot A[(⟨i, hi⟩ : Fin n)] x := by simp [matVec]
  rw [hmv]
  have hb : b[i] = b[(⟨i, hi⟩ : Fin n)] := rfl
  rw [hb]
  linarith

/-- `linSolve A b` is the only solution of `A x = b`. -/
theorem linSolve_unique (A : Mat ℝ n n) (b : Vec ℝ n)
    (hA : FullColumnRank A) (x : Vec ℝ n) (hx : matVec A x = b) :
    x = linSolve A b := by
  have hs := linSolve_spec A b hA
  have h0 := hA (vsub x (linSolve A b)) (by
    ext i hi
    have h1 := congrArg (·[i]) hx
    have h2 := congrArg (·[i]) hs
    simp only [matVec, Vector.getElem_ofFn] at h1 h2
    simp only [matVec, Vector.getElem_ofFn, vzero, dot_vsub, h1, h2, sub_self])
  ext i hi
  have := congrArg (·[i]) h0
  simpa [vsub, vzero, sub_eq_zero] using this

/-- `linSolve_spec` with Mathlib's determinant: `det A ≠ 0` suffices. -/
theorem linSolve_spec_of_det_ne_zero (A : Mat ℝ n n) (b : Vec ℝ n)
    (hdet : (Matrix.of fun i j : Fin n => A[i][j]).det ≠ 0) : matVec A (linSolve A b) = b := by
  refine linSolve_spec A b fun x hx => ?_
  have h := Matrix.eq_zero_of_mulVec_eq_zero hdet (v := fun j => x[j]) (by
    funext i
    have := congrArg (·[i]) hx
    simpa [matVec, vzero, dot_eq_sum, Matrix.mulVec, dotProduct] using this)
  ext i hi
  simpa [vzero] using congrFun h ⟨i, hi⟩

end LinSolve

end Primitives

end
