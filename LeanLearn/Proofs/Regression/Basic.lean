/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
-/
module

public import LeanLearn.Regression.Solvers
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# LeanLearn.Proofs.Regression.Basic

Linear regression — the loss is an exact quadratic.

Over `ℝ`, for a problem `P` with normal equations `A θ = b` (`A = P.normalMatrix`,
`b = P.normalVector`) and ridge penalty `λ`:

* **Entries** (`normalMatrix_apply`, `normalVector_apply`, `residual_apply`): the executable
  folds are the textbook sums — over any field, so also at `ℚ`, where the certificates run.
* **Exact expansion** (`loss_add`): `L(θ + v) = L(θ) + 2 ⟪A θ - b, v⟫ + C(v)`, where the
  *curvature* `C(v) = (1/m) ∑ᵣ ⟪xᵣ, v⟫² + λ ‖v‖²` is `vᵀ A v` (`curvature_eq`) and is
  non-negative for `λ ≥ 0`. So the loss is convex and `A θ - b` is half its gradient.
* **Optimality** (`loss_le_of_residual_eq_zero`): a solution of the normal equations
  minimises the loss over all parameters, and `L(u) - L(θ*) = C(u - θ*)` exactly.
* **Smoothness** (`curvature_le`): `C(v) ≤ Λ ‖v‖²` with `Λ = (1/m) ∑ᵣ ‖xᵣ‖² + λ`.
* **Degenerate coordinates** (`residual_eq_zero_of_diag_eq_zero`): if `Aᵢᵢ = 0` then the
  `i`-th equation is `0 = 0`, so Jacobi and Gauss–Seidel lose nothing by dividing by zero.
-/

@[expose] public section

namespace LeanLearn.Regression

open Finset

/-! ## Sums -/

section Sums

variable {K : Type} {n : ℕ}

/-- The executable count `count k` is the cast `(k : K)`, so `/ count m` reads as `/ m`: over any
additive monoid with one `K` (`ℝ` for the proofs, `ℚ` for the certificates). -/
@[simp] theorem count_eq_natCast [AddMonoidWithOne K] [Mul K] [Sub K] (k : ℕ) :
    (count k : K) = k := by
  induction k with
  | zero => simp [count, nsmulGen]
  | succ k ih => rw [count, nsmulGen, ← count, ih, ← Nat.cast_one, ← Nat.cast_add, Nat.add_comm]

/-- The executable inner product `dot u v` is the `Finset` sum `∑ᵢ uᵢ vᵢ`, over any additive
commutative monoid `K` (`ℝ` for the proofs, `ℚ` for the certificates). -/
theorem dot_eq_sum [AddCommMonoid K] [Mul K] [Sub K] [One K] (u v : Vec K n) :
    dot u v = ∑ i : Fin n, u[i] * v[i] :=
  sumFin_eq_sum _

/-- `⟪v, v⟫ = ‖v‖²` is non-negative. -/
theorem dot_self_nonneg (v : Vec ℝ n) : 0 ≤ dot v v := by
  rw [dot_eq_sum]
  exact sum_nonneg fun i _ ↦ mul_self_nonneg _

/-- Entry `i` of `vadd u v` is `uᵢ + vᵢ`. -/
@[simp] theorem vadd_getElem (u v : Vec ℝ n) (i : Fin n) : (vadd u v)[i] = u[i] + v[i] := by
  simp [vadd]

/-- Entry `i` of `vsub u v` is `uᵢ - vᵢ`, for any `PolynomialLike K` (`ℝ` for the proofs, `ℚ`
for the certificates). -/
@[simp] theorem vsub_getElem [PolynomialLike K] (u v : Vec K n) (i : Fin n) :
    (vsub u v)[i] = u[i] - v[i] := by
  simp [vsub]

/-- Entry `i` of `smul c v` is `c * vᵢ`. -/
@[simp] theorem smul_getElem (c : ℝ) (v : Vec ℝ n) (i : Fin n) : (smul c v)[i] = c * v[i] := by
  simp [smul]

/-- Every entry of `vzero` is `0`. -/
@[simp] theorem vzero_getElem (i : Fin n) : (vzero : Vec ℝ n)[i] = 0 := by
  simp [vzero]

/-! The same with natural-number indices, the form `simp` normalises to. -/

/-- `vadd_getElem` at a natural-number index. -/
@[simp] theorem vadd_getElem' (u v : Vec ℝ n) (i : ℕ) (h : i < n) :
    (vadd u v)[i] = u[i] + v[i] := by simp [vadd]

/-- `vsub_getElem` at a natural-number index. -/
@[simp] theorem vsub_getElem' (u v : Vec ℝ n) (i : ℕ) (h : i < n) :
    (vsub u v)[i] = u[i] - v[i] := by simp [vsub]

/-- `smul_getElem` at a natural-number index. -/
@[simp] theorem smul_getElem' (c : ℝ) (v : Vec ℝ n) (i : ℕ) (h : i < n) :
    (smul c v)[i] = c * v[i] := by simp [smul]

/-- `vzero_getElem` at a natural-number index. -/
@[simp] theorem vzero_getElem' (i : ℕ) (h : i < n) : (vzero : Vec ℝ n)[i] = 0 := by
  simp [vzero]

/-- Entry `i` of `matVec A v` is row `i` of `A` dotted with `v`, as a `Finset` sum: over any
additive commutative monoid `K` (`ℝ` for the proofs, `ℚ` for the certificates). -/
theorem matVec_getElem [AddCommMonoid K] [Mul K] [Sub K] [One K] {m : ℕ} (A : Mat K m n)
    (v : Vec K n) (i : Fin m) : (matVec A v)[i] = ∑ j : Fin n, A[i][j] * v[j] := by
  simp [matVec, dot_eq_sum]

/-- The inner product is additive in its second argument. -/
theorem dot_vadd (u v w : Vec ℝ n) : dot u (vadd v w) = dot u v + dot u w := by
  simp only [dot_eq_sum, vadd_getElem, mul_add, sum_add_distrib]

/-- The inner product is homogeneous in its second argument. -/
theorem dot_smul (u v : Vec ℝ n) (c : ℝ) : dot u (smul c v) = c * dot u v := by
  simp only [dot_eq_sum, smul_getElem, mul_sum, mul_left_comm]

/-- Vectors with the same entry at every `Fin n` index are equal: `Vector.ext` with a `Fin`
index instead of a bounded natural number, for any entry type `K` (`ℝ` for the proofs, `ℚ` for
the certificates). -/
theorem vext {u v : Vec K n} (h : ∀ i : Fin n, u[i] = v[i]) : u = v :=
  Vector.ext fun i hi ↦ h ⟨i, hi⟩

/-- Adding a difference back: `θ + (u - θ) = u`. -/
@[simp] theorem vadd_vsub_cancel (θ u : Vec ℝ n) : vadd θ (vsub u θ) = u :=
  vext fun i ↦ by simp

end Sums

/-! ## The problem's entries -/

namespace Problem

variable {K : Type} {m d : ℕ}

/-! ### Over any scalar: `ℝ` for the proofs, `ℚ` for the certificates -/

/-- Entry `i` of sample `r` with the constant `1` appended. -/
abbrev feature [PolynomialLike K] (P : Problem K m d) (r : Fin m) (i : Fin (d + 1)) : K :=
  (P.row r)[i]

/-- The fitted value `⟪xᵣ, θ⟫`. -/
abbrev fitted [PolynomialLike K] (P : Problem K m d) (r : Fin m) (θ : Vec K (d + 1)) : K :=
  dot (P.row r) θ

/-- The fitted value as a `Finset` sum, `⟪xᵣ, θ⟫ = ∑ᵢ xᵣᵢ θᵢ`, over any additive commutative
monoid `K`. -/
theorem fitted_eq [AddCommMonoid K] [Mul K] [Sub K] [One K] (P : Problem K m d) (r : Fin m)
    (θ : Vec K (d + 1)) : P.fitted r θ = ∑ i, P.feature r i * θ[i] :=
  dot_eq_sum _ _

/-- Entry `(i, j)` of the normal matrix `A = (1/m) ∑ᵣ xᵣ xᵣᵀ + λ I`: the executable fold read
as a `Finset` sum, over any division ring `K` (`ℝ` for the proofs, `ℚ` for the certificates). -/
theorem normalMatrix_apply [DivisionRing K] (P : Problem K m d) (i j : Fin (d + 1)) :
    P.normalMatrix[i][j] =
      (∑ r, P.feature r i * P.feature r j) / m + if i = j then P.ridge else 0 := by
  simp [normalMatrix, design, sumFin_eq_sum]

/-- Entry `i` of the normal vector `b = (1/m) ∑ᵣ yᵣ xᵣ`: the executable fold read as a
`Finset` sum, over any division ring `K` (`ℝ` for the proofs, `ℚ` for the certificates). -/
theorem normalVector_apply [DivisionRing K] (P : Problem K m d) (i : Fin (d + 1)) :
    P.normalVector[i] = (∑ r, P.feature r i * P.y[r]) / m := by
  simp [normalVector, design, sumFin_eq_sum]

/-- `∑ⱼ (∑ᵣ xᵣᵢ xᵣⱼ) θⱼ = ∑ᵣ xᵣᵢ ⟪xᵣ, θ⟫`, over any ring `K` (`ℝ` for the proofs, `ℚ` for the
certificates). -/
theorem sum_gram_mul [Ring K] (P : Problem K m d) (i : Fin (d + 1)) (θ : Vec K (d + 1)) :
    ∑ j : Fin (d + 1), (∑ r, P.feature r i * P.feature r j) * θ[j] =
      ∑ r, P.feature r i * P.fitted r θ := by
  simp only [fitted_eq, sum_mul, mul_sum, mul_assoc]
  exact sum_comm

/-- The residual of the normal equations, `(A θ - b)ᵢ`, over any field `K` (`ℝ` for the proofs,
`ℚ` for the certificates). -/
theorem residual_apply [Field K] (P : Problem K m d) (θ : Vec K (d + 1)) (i : Fin (d + 1)) :
    (residual P.normalMatrix P.normalVector θ)[i] =
      (∑ r, P.feature r i * (P.fitted r θ - P.y[r])) / m + P.ridge * θ[i] := by
  simp only [residual, vsub_getElem, matVec_getElem, normalVector_apply, normalMatrix_apply,
    add_mul, ite_mul, zero_mul, sum_add_distrib, sum_ite_eq, mem_univ, if_true,
    div_mul_eq_mul_div, ← sum_div, sum_gram_mul, mul_sub, sum_sub_distrib]
  ring

/-! ### Over `ℝ` -/

variable (P : Problem ℝ m d)

/-- Row `r` of the design matrix is sample `r` with the constant `1` appended. -/
@[simp] theorem design_getElem (r : Fin m) : P.design[r] = P.row r := by
  simp [design]

/-- The normal matrix is symmetric. -/
theorem normalMatrix_symm (i j : Fin (d + 1)) : P.normalMatrix[i][j] = P.normalMatrix[j][i] := by
  simp only [normalMatrix_apply, mul_comm, eq_comm]

/-- The ridge loss as `Finset` sums, `L(θ) = (1/m) ∑ᵣ (⟪xᵣ, θ⟫ - yᵣ)² + λ ‖θ‖²`: the shape every
bound in this file starts from. -/
theorem loss_eq (θ : Vec ℝ (d + 1)) :
    P.loss θ = (∑ r, (P.fitted r θ - P.y[r]) ^ 2) / m + P.ridge * ∑ i : Fin (d + 1), θ[i] ^ 2 := by
  simp only [loss, sumFin_eq_sum, count_eq_natCast, sq, dot_eq_sum]

/-- The curvature `C(v) = (1/m) ∑ᵣ ⟪xᵣ, v⟫² + λ ‖v‖²`: the second-order part of the
loss. -/
noncomputable def curvature (v : Vec ℝ (d + 1)) : ℝ :=
  (∑ r, P.fitted r v ^ 2) / m + P.ridge * ∑ i : Fin (d + 1), v[i] ^ 2

/-- For `λ ≥ 0` the curvature is non-negative: the loss is convex. -/
theorem curvature_nonneg (hridge : 0 ≤ P.ridge) (v : Vec ℝ (d + 1)) : 0 ≤ P.curvature v :=
  add_nonneg (div_nonneg (sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg m))
    (mul_nonneg hridge (sum_nonneg fun _ _ ↦ sq_nonneg _))

/-- The curvature is a quadratic form: `C(c v) = c² C(v)`. -/
theorem curvature_smul (c : ℝ) (v : Vec ℝ (d + 1)) :
    P.curvature (smul c v) = c ^ 2 * P.curvature v := by
  simp only [curvature, dot_smul, smul_getElem, mul_pow, ← mul_sum]
  ring

/-- `∑ᵢ (A θ - b)ᵢ vᵢ = (1/m) ∑ᵣ (⟪xᵣ, θ⟫ - yᵣ) ⟪xᵣ, v⟫ + λ ⟪θ, v⟫`. -/
theorem sum_residual_mul (θ v : Vec ℝ (d + 1)) :
    ∑ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] * v[i] =
      (∑ r, (P.fitted r θ - P.y[r]) * P.fitted r v) / m +
        P.ridge * ∑ i : Fin (d + 1), θ[i] * v[i] := by
  simp only [residual_apply, add_mul, sum_add_distrib, div_mul_eq_mul_div, ← sum_div, mul_assoc,
    ← mul_sum]
  congr 2
  simp only [fitted_eq, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun r _ ↦ sum_congr rfl fun i _ ↦ by ring

/-- **The loss is an exact quadratic**: `L(θ + v) = L(θ) + 2 ⟪A θ - b, v⟫ + C(v)`. -/
theorem loss_add (θ v : Vec ℝ (d + 1)) :
    P.loss (vadd θ v) = P.loss θ +
      2 * ∑ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] * v[i] +
        P.curvature v := by
  rw [sum_residual_mul, loss_eq, loss_eq, curvature]
  have h1 : ∀ a b c : ℝ, (a + b - c) ^ 2 = (a - c) ^ 2 + 2 * ((a - c) * b) + b ^ 2 :=
    fun a b c ↦ by ring
  have h2 : ∀ a b : ℝ, (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := fun a b ↦ by ring
  simp only [fitted, dot_vadd, vadd_getElem, h1, h2, sum_add_distrib, ← mul_sum]
  ring

/-- **Convexity**: the loss lies above its tangent planes. -/
theorem tangent_le_loss (hridge : 0 ≤ P.ridge) (θ u : Vec ℝ (d + 1)) :
    P.loss θ + 2 * ∑ i : Fin (d + 1),
      (residual P.normalMatrix P.normalVector θ)[i] * (u[i] - θ[i]) ≤ P.loss u := by
  have h := P.loss_add θ (vsub u θ)
  simp only [vadd_vsub_cancel, vsub_getElem] at h
  linarith [P.curvature_nonneg hridge (vsub u θ)]

/-- **A posteriori bound**: for `λ > 0`, any `θ` is within `‖A θ - b‖² / λ` of the loss of
every `u`. After training, the residual is the only thing that needs checking, whatever
produced `θ`: `L(u) - L(θ) = 2 ⟪r, v⟫ + C(v) ≥ 2 ⟪r, v⟫ + λ ‖v‖² ≥ -‖r‖² / λ` for `v = u - θ`. -/
theorem loss_le_add_residual (hridge : 0 < P.ridge) (θ u : Vec ℝ (d + 1)) :
    P.loss θ ≤ P.loss u +
      (∑ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] ^ 2) / P.ridge := by
  have h := P.loss_add θ (vsub u θ)
  rw [vadd_vsub_cancel, curvature] at h
  have hF : 0 ≤ (∑ s, P.fitted s (vsub u θ) ^ 2) / m :=
    div_nonneg (sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg m)
  -- `0 ≤ ∑ᵢ (rᵢ + λ vᵢ)²`, expanded
  have hsq : 0 ≤ ∑ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] ^ 2 +
      2 * P.ridge * ∑ i : Fin (d + 1),
        (residual P.normalMatrix P.normalVector θ)[i] * (vsub u θ)[i] +
      P.ridge ^ 2 * ∑ i : Fin (d + 1), (vsub u θ)[i] ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_nonneg fun i _ ↦ ?_
    linarith [sq_nonneg ((residual P.normalMatrix P.normalVector θ)[i] + P.ridge * (vsub u θ)[i])]
  rw [← sub_le_iff_le_add', le_div_iff₀ hridge, h]
  linarith [hsq, mul_nonneg hridge.le hF]

/-- **Optimality**: a solution of the normal equations minimises the loss, and the
excess loss of any `u` is exactly `C(u - θ*)`. -/
theorem loss_eq_of_residual_eq_zero {θ : Vec ℝ (d + 1)}
    (h : ∀ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] = 0)
    (u : Vec ℝ (d + 1)) : P.loss u = P.loss θ + P.curvature (vsub u θ) := by
  simpa only [vadd_vsub_cancel, h, zero_mul, sum_const_zero, mul_zero, add_zero] using
    P.loss_add θ (vsub u θ)

/-- **Optimality** as an inequality: for `λ ≥ 0`, a solution of the normal equations has the
least loss of all parameters — the `≤` form of `loss_eq_of_residual_eq_zero`. -/
theorem loss_le_of_residual_eq_zero (hridge : 0 ≤ P.ridge) {θ : Vec ℝ (d + 1)}
    (h : ∀ i : Fin (d + 1), (residual P.normalMatrix P.normalVector θ)[i] = 0)
    (u : Vec ℝ (d + 1)) : P.loss θ ≤ P.loss u := by
  rw [P.loss_eq_of_residual_eq_zero h u]
  linarith [P.curvature_nonneg hridge (vsub u θ)]

/-- The curvature is the quadratic form of `A`: `C(v) = vᵀ A v`. -/
theorem curvature_eq (v : Vec ℝ (d + 1)) :
    P.curvature v = ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), P.normalMatrix[i][j] * v[i] * v[j] := by
  simp only [normalMatrix_apply, add_mul, sum_add_distrib, curvature, fitted_eq]
  congr 1
  · simp only [div_mul_eq_mul_div, ← sum_div, sq, sum_mul, mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun r _ ↦ ?_
    rw [sum_comm]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  · simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true, mul_sum, sq]
    exact sum_congr rfl fun i _ ↦ by ring

/-- **Smoothness**: `C(v) ≤ Λ ‖v‖²` with `Λ = (1/m) ∑ᵣ ‖xᵣ‖² + λ` (Cauchy–Schwarz on every
sample). -/
theorem curvature_le (v : Vec ℝ (d + 1)) :
    P.curvature v ≤
      ((∑ r, ∑ i, P.feature r i ^ 2) / m + P.ridge) * ∑ i : Fin (d + 1), v[i] ^ 2 := by
  rw [curvature, add_mul, div_mul_eq_mul_div, sum_mul]
  gcongr with r _
  rw [fitted_eq]
  exact sum_mul_sq_le_sq_mul_sq _ _ _

/-- If `Aᵢᵢ = 0` (with `λ ≥ 0`), the penalty is `0`: `Aᵢᵢ = (1/m) ∑ᵣ xᵣᵢ² + λ` is a sum of two
non-negative terms. -/
theorem ridge_eq_zero_of_diag_eq_zero (hridge : 0 ≤ P.ridge) {i : Fin (d + 1)}
    (hA : P.normalMatrix[i][i] = 0) : P.ridge = 0 := by
  rw [normalMatrix_apply, if_pos rfl] at hA
  have hs : 0 ≤ (∑ r, P.feature r i * P.feature r i) / m :=
    div_nonneg (sum_nonneg fun _ _ ↦ mul_self_nonneg _) (Nat.cast_nonneg m)
  linarith

/-- If `Aᵢᵢ = 0` (with `λ ≥ 0`), feature `i` is zero on every sample. -/
theorem feature_eq_zero_of_diag_eq_zero (hridge : 0 ≤ P.ridge) {i : Fin (d + 1)}
    (hA : P.normalMatrix[i][i] = 0) (r : Fin m) : P.feature r i = 0 := by
  have hridge0 := P.ridge_eq_zero_of_diag_eq_zero hridge hA
  rw [normalMatrix_apply, if_pos rfl, hridge0, add_zero, div_eq_zero_iff,
    or_iff_left (Nat.cast_ne_zero.mpr r.pos.ne')] at hA
  exact mul_self_eq_zero.mp
    ((sum_eq_zero_iff_of_nonneg fun _ _ ↦ mul_self_nonneg _).mp hA r (mem_univ r))

/-- If `Aᵢᵢ = 0` (with `λ ≥ 0`), the `i`-th residual vanishes for every `θ`: feature `i` is zero
on every sample and unpenalised, so equation `i` reads `0 = 0` and Jacobi and Gauss–Seidel lose
nothing by leaving coordinate `i` alone. -/
theorem residual_eq_zero_of_diag_eq_zero (hridge : 0 ≤ P.ridge) {i : Fin (d + 1)}
    (hA : P.normalMatrix[i][i] = 0) (θ : Vec ℝ (d + 1)) :
    (residual P.normalMatrix P.normalVector θ)[i] = 0 := by
  rw [residual_apply, P.ridge_eq_zero_of_diag_eq_zero hridge hA]
  simp [P.feature_eq_zero_of_diag_eq_zero hridge hA]

/-- If `Aᵢᵢ = 0` (with `λ ≥ 0`), the whole row `i` of `A` vanishes: the curvature does not see
coordinate `i`. -/
theorem normalMatrix_row_eq_zero (hridge : 0 ≤ P.ridge) {i : Fin (d + 1)}
    (hA : P.normalMatrix[i][i] = 0) (j : Fin (d + 1)) : P.normalMatrix[i][j] = 0 := by
  rw [normalMatrix_apply, P.ridge_eq_zero_of_diag_eq_zero hridge hA]
  simp [P.feature_eq_zero_of_diag_eq_zero hridge hA]

end Problem

end LeanLearn.Regression
