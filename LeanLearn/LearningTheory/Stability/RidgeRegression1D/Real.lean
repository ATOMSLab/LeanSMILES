/-
Copyright (c) 2026 TorchLean
Released under MIT license as described in the file LICENSES/TorchLean-MIT.txt.
Authors: TorchLean Team
-/

module

public import LeanLearn.LearningTheory.Stability.Core

/-!
# 1D ridge regression: replace-one uniform stability (squared loss)

This file is a self-contained, fully formalized worked example:

- we define the *closed-form* 1D ridge-regression estimator, and
- we prove a deterministic **replace-one uniform stability** bound for the squared loss, under
  bounded inputs.

## Proof outline (informal)

At a high level, the uniform stability proof follows the standard “strongly convex ERM is stable”
template, specialized to the 1D closed-form ridge solution:

1. Express $\widehat w(S)$ and $\widehat w(S')$ as ratios of sums
   $\mathrm{sumXY}/(\mathrm{sumXX}+\lambda N)$.
2. Bound how much the numerator `sumXY` and denominator `sumXX` can change when one example is
   replaced (via a simple finite-sum perturbation lemma).
3. Bound the change in the reciprocal of the denominator, hence bound
   $|\widehat w(S)-\widehat w(S')|$.
4. Translate a bound on $|w-w'|$ into a bound on the loss change for the squared loss
   $(wx-y)^2$ by factoring a difference of squares.

## Ridge regression in 1D (math)

Each example is a pair $(x,y)\in\mathbb R\times\mathbb R$. For a dataset $S$ of size $N$, ridge
regression with regularization parameter $\lambda>0$ minimizes

$$
\frac1N\sum_i(wx_i-y_i)^2+\lambda w^2.
$$

In 1D, the minimizer has the familiar closed form

$$
\widehat w(S)=\frac{\sum_i x_i y_i}{\sum_i x_i^2+\lambda N}.
$$

In this file we set $N=n+1$ (so indices are `Fin (n+1)`), because “remove-at” and “replace-at”
operations are most convenient in that convention in our `Dataset` library.

## Datasets

In `Stability.Core`, a dataset `Dataset N Z` is a function `Fin N → Z`.
We use `Dataset.get S i` to access the `i`-th example.

## Stability statement (informal)

Let $S'$ be $S$ with one example replaced. If inputs satisfy $|x|\le X$ and $|y|\le Y$, then
for any test point $z$ we bound

$|\ell(\widehat w(S),z)-\ell(\widehat w(S'),z)|$,

where $\ell(w,(x,y))=(wx-y)^2$.

The final bound is $4X^2Y^2(\lambda+X^2)^2/(\lambda^3 N)$. It scales as $1/N$ for fixed
$X,Y,\lambda>0$; its dependence on $\lambda$ includes inverse-cubic terms, so it is not a
uniform $O(1/(\lambda N))$ estimate as $\lambda$ tends to zero.

This is intended as a small, fully proved example that can be cited in documentation/papers.

## References / citations (informal pointers)

- Ridge/Tikhonov regularization: Tikhonov (1963); Hoerl & Kennard (1970), “Ridge Regression: Biased
  Estimation…”.
- Stability and generalization: Bousquet & Elisseeff (2002), “Stability and Generalization”.
- Stability for regularized ERM / strong convexity: Shalev-Shwartz et al. (2010), “Learnability,
  Stability and Uniform Convergence”.
- For additional viewpoints on stability and generalization, see also: Poggio, Rifkin, Mukherjee &
  Niyogi (2004), “General conditions for predictivity in learning theory”.

## Provenance

Extracted from TorchLean (`NN/MLTheory/LearningTheory/Stability/RidgeRegression1D/Real.lean`,
`main` at `772b6b8`), MIT-licensed; see `LICENSES/TorchLean-MIT.txt`. The code is unchanged apart
from the `LeanSMILES` namespace and import paths; it runs on `Stability.Core`'s `Dataset`, which is
`Fin n → Z` here rather than TorchLean's tensor. For this project's Mathlib (`v4.30.0-rc1`),
`sum_replaceAt_sub` uses `if_neg`/`if_pos` for `ite_eq_right`/`ite_eq_left`, and four blank lines
inside the main proof are removed for `linter.style.emptyLine`.
-/

@[expose] public section


noncomputable section

open scoped BigOperators

namespace LeanLearn.LearningTheory.Stability.RidgeRegression1D

variable {n : Nat}

/-! ## Bounded examples -/

/--
An example $(x,y)$ together with bounds $|x|\le X$ and $|y|\le Y$.

This lets us state stability bounds as theorems with explicit constants in terms of `X` and `Y`.
The bounds are carried in the subtype, so every lemma below can use them without repeating
hypotheses.
-/
def BoundedExample (X Y : ℝ) : Type :=
  {p : ℝ × ℝ // |p.1| ≤ X ∧ |p.2| ≤ Y}

namespace BoundedExample

variable {X Y : ℝ}

/-- The `x` coordinate of a bounded example. -/
@[simp] def x (z : BoundedExample X Y) : ℝ := z.1.1
/-- The `y` coordinate of a bounded example. -/
@[simp] def y (z : BoundedExample X Y) : ℝ := z.1.2

/-- The `x` coordinate satisfies the declared bound $|x|\le X$. -/
theorem abs_x_le (z : BoundedExample X Y) : |z.x| ≤ X := z.2.1
/-- The `y` coordinate satisfies the declared bound $|y|\le Y$. -/
theorem abs_y_le (z : BoundedExample X Y) : |z.y| ≤ Y := z.2.2

/-- The declared bound `X` is nonnegative because $|x|\le X$. -/
theorem X_nonneg (z : BoundedExample X Y) : 0 ≤ X :=
  le_trans (abs_nonneg z.x) z.abs_x_le

/-- The declared bound `Y` is nonnegative because $|y|\le Y$. -/
theorem Y_nonneg (z : BoundedExample X Y) : 0 ≤ Y :=
  le_trans (abs_nonneg z.y) z.abs_y_le

/-- The cross term of a bounded example satisfies $|xy|\le XY$. -/
theorem abs_x_mul_y_le (z : BoundedExample X Y) : |z.x * z.y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul z.abs_x_le z.abs_y_le (abs_nonneg _) z.X_nonneg

/-- The squared input of a bounded example satisfies $x^2\le X^2$. -/
theorem sq_x_le (z : BoundedExample X Y) : z.x ^ 2 ≤ X ^ 2 := by
  rw [← sq_abs z.x]
  exact pow_le_pow_left₀ (abs_nonneg _) z.abs_x_le 2

end BoundedExample

/-! ## Sums and estimator -/

section

variable {X Y : ℝ}

/-- Sum of squares $\sum_i x_i^2$. -/
def sumXX (S : Dataset (n + 1) (BoundedExample X Y)) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), (Dataset.get S i).x ^ 2

/-- Cross-term sum $\sum_i x_i y_i$. -/
def sumXY (S : Dataset (n + 1) (BoundedExample X Y)) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), (Dataset.get S i).x * (Dataset.get S i).y

/--
Closed-form 1D ridge fit.

$\operatorname{ridgeFit1D}(\lambda,S)
=\frac{\sum_i x_i y_i}{\sum_i x_i^2+\lambda N}$, where $N=n+1$.
-/
def ridgeFit1D (lam : ℝ) (S : Dataset (n + 1) (BoundedExample X Y)) : ℝ :=
  let N : ℝ := ((n + 1 : Nat) : ℝ)
  (sumXY (n := n) S) / (sumXX (n := n) S + lam * N)

/-- Squared loss $\ell(w,(x,y))=(wx-y)^2$. -/
def sqLoss (w : ℝ) (z : BoundedExample X Y) : ℝ :=
  (w * z.x - z.y) ^ 2

end

/-! ## Generic “sum changes at one index” lemma -/

section

/--
Replacing a single element of a dataset changes a sum over the dataset by a single-term
difference.

This finite-sum perturbation identity is the combinatorial input needed to control `sumXX` and
`sumXY` under replace-one.
-/
private theorem sum_replaceAt_sub {Z : Type} (φ : Z → ℝ)
    (S : Dataset (n + 1) Z) (i : Fin (n + 1)) (z' : Z) :
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))), φ (Dataset.get S j)) -
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))), φ (Dataset.get (replaceAt S i z') j)) =
      φ (Dataset.get S i) - φ z' := by
  -- Only the summand at `i` survives the difference, since `get_replaceAt` is the identity
  -- elsewhere.
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i
    (fun j _ hj => by rw [get_replaceAt, if_neg hj, sub_self]) (by simp)]
  rw [get_replaceAt, if_pos rfl]

end

/-! ## Ridge stability proof -/

namespace Ridge1D

variable {X Y lam : ℝ}

/-!
Everything below is “analysis lemmas” that culminate in the final uniform stability theorem.
The section exposes the headline theorem while keeping intermediate constants and algebraic bounds
local to the proof.
-/

/-- The sample size `n + 1` as a real number, so the averaging denominators stay readable. -/
def N : ℝ := ((n + 1 : Nat) : ℝ)

/-- $N=n+1$ is positive as a real number. -/
theorem N_pos : 0 < N (n := n) := by
  simpa [N] using (Nat.cast_pos.mpr (Nat.succ_pos n))

/-- `sumXX` is nonnegative (it is a sum of squares). -/
private theorem sumXX_nonneg (S : Dataset (n + 1) (BoundedExample X Y)) :
    0 ≤ sumXX (n := n) S := by
  unfold sumXX
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/--
The ridge denominator $\operatorname{sumXX}(S)+\lambda N$ is positive when $\lambda>0$.

This ensures the closed-form ratio is well-defined and lets us use order properties of division.
-/
private theorem denom_pos (hlam : 0 < lam) (S : Dataset (n + 1) (BoundedExample X Y)) :
    0 < sumXX (n := n) S + lam * N (n := n) := by
  have h1 : 0 ≤ sumXX (n := n) S := sumXX_nonneg (n := n) (X := X) (Y := Y) S
  have h2 : 0 < lam * N (n := n) := mul_pos hlam (N_pos (n := n))
  linarith

/--
Lower bound on the ridge denominator: $\lambda N\le\operatorname{sumXX}(S)+\lambda N$.

We use this to replace the (dataset-dependent) denominator with a uniform lower bound.
-/
private theorem denom_lower (S : Dataset (n + 1) (BoundedExample X Y)) :
    lam * N (n := n) ≤ sumXX (n := n) S + lam * N (n := n) := by
  have h1 : 0 ≤ sumXX (n := n) S := sumXX_nonneg (n := n) (X := X) (Y := Y) S
  linarith

/-- Absolute bound on the cross-term sum `sumXY`, from the bounds $|x|\le X$ and $|y|\le Y$. -/
private theorem abs_sumXY_le (S : Dataset (n + 1) (BoundedExample X Y)) :
    |sumXY (n := n) S| ≤ N (n := n) * X * Y := by
  classical
  calc
    |sumXY (n := n) S|
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), |(Dataset.get S i).x * (Dataset.get S i).y| :=
          by
            simpa [sumXY] using
              (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin (n + 1))))
                (f := fun i => (Dataset.get S i).x * (Dataset.get S i).y))
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin (n + 1))), (X * Y) :=
          Finset.sum_le_sum fun i _ => (Dataset.get S i).abs_x_mul_y_le
    _ = ((n + 1 : Nat) : ℝ) * (X * Y) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = N (n := n) * X * Y := by
          simp [N]
          ring_nf

/--
Replacing one example changes `sumXY` by at most $2XY$: the numerator perturbation bound for the
ridge closed form.
-/
private theorem abs_sumXY_sub_replaceAt_le (S : Dataset (n + 1) (BoundedExample X Y))
    (i : Fin (n + 1)) (z' : BoundedExample X Y) :
    |sumXY (n := n) S - sumXY (n := n) (replaceAt S i z')| ≤ 2 * X * Y := by
  classical
  have hdiff :
      sumXY (n := n) S - sumXY (n := n) (replaceAt S i z') =
        (Dataset.get S i).x * (Dataset.get S i).y - z'.x * z'.y := by
    have := sum_replaceAt_sub (φ := fun z : BoundedExample X Y => z.x * z.y) S i z'
    simpa [sumXY] using this
  calc
    |sumXY (n := n) S - sumXY (n := n) (replaceAt S i z')|
        = |(Dataset.get S i).x * (Dataset.get S i).y - z'.x * z'.y| := by rw [hdiff]
    _ ≤ |(Dataset.get S i).x * (Dataset.get S i).y| + |z'.x * z'.y| := abs_sub _ _
    _ ≤ X * Y + X * Y := add_le_add (Dataset.get S i).abs_x_mul_y_le z'.abs_x_mul_y_le
    _ = 2 * X * Y := by ring

/--
Replacing one example changes `sumXX` by at most $2X^2$: the denominator perturbation bound for
the ridge closed form.
-/
private theorem abs_sumXX_sub_replaceAt_le (S : Dataset (n + 1) (BoundedExample X Y))
    (i : Fin (n + 1)) (z' : BoundedExample X Y) :
    |sumXX (n := n) S - sumXX (n := n) (replaceAt S i z')| ≤ 2 * X ^ 2 := by
  classical
  have hdiff :
      sumXX (n := n) S - sumXX (n := n) (replaceAt S i z') =
        (Dataset.get S i).x ^ 2 - z'.x ^ 2 := by
    have := sum_replaceAt_sub (φ := fun z : BoundedExample X Y => z.x ^ 2) S i z'
    simpa [sumXX] using this
  calc
    |sumXX (n := n) S - sumXX (n := n) (replaceAt S i z')|
        = |(Dataset.get S i).x ^ 2 - z'.x ^ 2| := by rw [hdiff]
    _ ≤ |(Dataset.get S i).x ^ 2| + |z'.x ^ 2| := abs_sub _ _
    _ = (Dataset.get S i).x ^ 2 + z'.x ^ 2 := by simp
    _ ≤ X ^ 2 + X ^ 2 := add_le_add (Dataset.get S i).sq_x_le z'.sq_x_le
    _ = 2 * X ^ 2 := by ring

/--
Bound the magnitude of the fitted ridge weight.

This is a coarse bound of the form $|\widehat w(S)|\le XY/\lambda$.
-/
private theorem abs_w_le (hlam : 0 < lam) (S : Dataset (n + 1) (BoundedExample X Y)) :
    |ridgeFit1D (n := n) (X := X) (Y := Y) lam S| ≤ (X * Y) / lam := by
  classical
  set D : ℝ := sumXX (n := n) (X := X) (Y := Y) S + lam * N (n := n)
  have hDpos : 0 < D := by
    simpa [D] using (denom_pos (n := n) (X := X) (Y := Y) (lam := lam) hlam S)
  have hDge : lam * N (n := n) ≤ D := by
    simpa [D] using (denom_lower (n := n) (X := X) (Y := Y) (lam := lam) S)
  have hlamNpos : 0 < lam * N (n := n) := mul_pos hlam (N_pos (n := n))
  have hB : |sumXY (n := n) (X := X) (Y := Y) S| ≤ N (n := n) * X * Y :=
    abs_sumXY_le (n := n) (X := X) (Y := Y) S
  have habsD : |D| = D := abs_of_pos hDpos
  have hfit :
      ridgeFit1D (n := n) (X := X) (Y := Y) lam S = sumXY (n := n) (X := X) (Y := Y) S / D := by
    simp [ridgeFit1D, D, N]
  have hpos_num : 0 ≤ |sumXY (n := n) (X := X) (Y := Y) S| := abs_nonneg _
  calc
      |ridgeFit1D (n := n) (X := X) (Y := Y) lam S|
          = |sumXY (n := n) (X := X) (Y := Y) S| / D := by
              -- `D > 0` removes `|D|` after `abs_div`.
              simp [hfit, abs_div, habsD]
    _ ≤ |sumXY (n := n) (X := X) (Y := Y) S| / (lam * N (n := n)) := by
          exact div_le_div_of_nonneg_left hpos_num hlamNpos hDge
    _ ≤ (N (n := n) * X * Y) / (lam * N (n := n)) := by
          exact div_le_div_of_nonneg_right hB (le_of_lt hlamNpos)
    _ = (X * Y) / lam := by
          have hNne : (N (n := n)) ≠ 0 := ne_of_gt (N_pos (n := n))
          field_simp [N, hNne, (ne_of_gt hlam)]

/--
Bound the residual $|\widehat w(S)x-y|$ at a test point.

This is another coarse bound used at the very end when bounding the loss change via
$(e-e')(e+e')$ for $e=wx-y$.
-/
private theorem abs_residual_le (hlam : 0 < lam) (S : Dataset (n + 1) (BoundedExample X Y))
    (z : BoundedExample X Y) :
    |ridgeFit1D (n := n) (X := X) (Y := Y) lam S * z.x - z.y| ≤ Y * (lam + X ^ 2) / lam := by
  have hw : |ridgeFit1D (n := n) (X := X) (Y := Y) lam S| ≤ (X * Y) / lam :=
    abs_w_le (n := n) (X := X) (Y := Y) (lam := lam) hlam S
  have hXYlam_nonneg : 0 ≤ (X * Y) / lam :=
    div_nonneg (mul_nonneg z.X_nonneg z.Y_nonneg) (le_of_lt hlam)
  calc
    |ridgeFit1D (n := n) (X := X) (Y := Y) lam S * z.x - z.y|
        ≤ |ridgeFit1D (n := n) (X := X) (Y := Y) lam S * z.x| + |z.y| := abs_sub _ _
    _ = |ridgeFit1D (n := n) (X := X) (Y := Y) lam S| * |z.x| + |z.y| := by
          rw [abs_mul]
    _ ≤ ((X * Y) / lam) * X + Y :=
          add_le_add (mul_le_mul hw z.abs_x_le (abs_nonneg _) hXYlam_nonneg) z.abs_y_le
    _ = Y * (lam + X ^ 2) / lam := by
          field_simp [(ne_of_gt hlam)]
          ring

/-!
## Main theorem: deterministic replace-one uniform stability

The next theorem is the headline result of this file. Its proof combines the parameter-sensitivity
and prediction-loss bounds established above.
-/

/--
**Uniform stability of 1D ridge regression (bounded inputs, squared loss).**

Assume $\lambda>0$. Then the ridge estimator `ridgeFit1D λ` is uniformly stable in the replace-one
sense for the squared loss, with bound
$\beta=4X^2Y^2(\lambda+X^2)^2/(\lambda^3 N)$, where $N=n+1$.
Training, replacement, and test examples all carry the same bounds $|x|\le X$, $|y|\le Y$.

The stability notion used here is `UniformStableReplace` from `Stability.Core`.
-/
theorem ridgeFit1D_sqLoss_uniformStableReplace (hlam : 0 < lam) :
    UniformStableReplace (Z := BoundedExample X Y) (H := ℝ)
      (A := fun S => ridgeFit1D (n := n) (X := X) (Y := Y) lam S)
      (ℓ := fun w z => sqLoss (X := X) (Y := Y) w z)
      (β := 4 * X ^ 2 * Y ^ 2 * (lam + X ^ 2) ^ 2 / (lam ^ 3 * N (n := n))) := by
  classical
  intro S i z z'
  set S' : Dataset (n + 1) (BoundedExample X Y) := replaceAt S i z'
  set w : ℝ := ridgeFit1D (n := n) (X := X) (Y := Y) lam S
  set w' : ℝ := ridgeFit1D (n := n) (X := X) (Y := Y) lam S'
  set D : ℝ := sumXX (n := n) (X := X) (Y := Y) S + lam * N (n := n)
  set D' : ℝ := sumXX (n := n) (X := X) (Y := Y) S' + lam * N (n := n)
  have hDpos : 0 < D := by
    simpa [D] using (denom_pos (n := n) (X := X) (Y := Y) (lam := lam) hlam S)
  have hD'pos : 0 < D' := by
    simpa [D'] using (denom_pos (n := n) (X := X) (Y := Y) (lam := lam) hlam S')
  have hDge : lam * N (n := n) ≤ D := by
    simpa [D] using (denom_lower (n := n) (X := X) (Y := Y) (lam := lam) S)
  have hD'ge : lam * N (n := n) ≤ D' := by
    simpa [D'] using (denom_lower (n := n) (X := X) (Y := Y) (lam := lam) S')
  have hlamNpos : 0 < lam * N (n := n) := mul_pos hlam (N_pos (n := n))
  have hBdiff :
      |sumXY (n := n) (X := X) (Y := Y) S - sumXY (n := n) (X := X) (Y := Y) S'| ≤ 2 * X * Y := by
    simpa [S'] using abs_sumXY_sub_replaceAt_le (n := n) (X := X) (Y := Y) S i z'
  have hB' : |sumXY (n := n) (X := X) (Y := Y) S'| ≤ N (n := n) * X * Y :=
    abs_sumXY_le (n := n) (X := X) (Y := Y) S'
  have hw_def : w = (sumXY (n := n) (X := X) (Y := Y) S) / D := by
    simp [w, ridgeFit1D, D, N]
  have hw'_def : w' = (sumXY (n := n) (X := X) (Y := Y) S') / D' := by
    simp [w', ridgeFit1D, D', N, S']
  -- Bound |1/D - 1/D'|
  have hA_diff :
      |sumXX (n := n) (X := X) (Y := Y) S - sumXX (n := n) (X := X) (Y := Y) S'| ≤ 2 * X ^ 2 := by
    simpa [S'] using abs_sumXX_sub_replaceAt_le (n := n) (X := X) (Y := Y) S i z'
  have hInv :
      |(1 / D) - (1 / D')| ≤ (2 * X ^ 2) / (lam ^ 2 * (N (n := n)) ^ 2) := by
    have hDne : D ≠ 0 := ne_of_gt hDpos
    have hD'ne : D' ≠ 0 := ne_of_gt hD'pos
    have hInvEq : (1 / D) - (1 / D') = (D' - D) / (D * D') := by
      simpa [one_div] using (inv_sub_inv (a := D) (b := D') hDne hD'ne)
    have hposDD' : 0 < D * D' := mul_pos hDpos hD'pos
    have hDD'ge : (lam * N (n := n)) ^ 2 ≤ D * D' := by
      nlinarith [hDge, hD'ge, le_of_lt hDpos, le_of_lt hD'pos]
    have hDdiff : |D' - D| ≤ 2 * X ^ 2 := by
      have hsub :
          D' - D = sumXX (n := n) (X := X) (Y := Y) S' - sumXX (n := n) (X := X) (Y := Y) S := by
        simp [D, D']
      rw [hsub, abs_sub_comm]
      exact hA_diff
    have hn : 0 ≤ 2 * X ^ 2 := by positivity
    calc
      |(1 / D) - (1 / D')|
          = |(D' - D) / (D * D')| := by
              simpa using congrArg abs hInvEq
      _ = |D' - D| / (D * D') := by simp [abs_div, abs_of_pos hposDD']
      _ ≤ (2 * X ^ 2) / (D * D') := by
            exact div_le_div_of_nonneg_right hDdiff (le_of_lt hposDD')
      _ ≤ (2 * X ^ 2) / ((lam * N (n := n)) ^ 2) := by
            exact div_le_div_of_nonneg_left hn (sq_pos_of_pos hlamNpos) hDD'ge
      _ = (2 * X ^ 2) / (lam ^ 2 * (N (n := n)) ^ 2) := by ring_nf
  -- Bound |w - w'|.
  have hw_diff :
      |w - w'| ≤ (2 * X * Y * (lam + X ^ 2)) / (lam ^ 2 * N (n := n)) := by
    have habsD : |D| = D := abs_of_pos hDpos
    have hterm1 :
        |(sumXY (n := n) (X := X) (Y := Y) S - sumXY (n := n) (X := X) (Y := Y) S') / D|
          ≤ (2 * X * Y) / (lam * N (n := n)) := by
      have h0 : 0 ≤ |sumXY (n := n) (X := X) (Y := Y) S - sumXY (n := n) (X := X) (Y := Y) S'| :=
        abs_nonneg _
      have : |(sumXY (n := n) (X := X) (Y := Y) S - sumXY (n := n) (X := X) (Y := Y) S') / D|
          = |sumXY (n := n) (X := X) (Y := Y) S - sumXY (n := n) (X := X) (Y := Y) S'| / D := by
            simp [abs_div, habsD]
      calc
        |(sumXY (n := n) (X := X) (Y := Y) S - sumXY (n := n) (X := X) (Y := Y) S') / D|
            = |sumXY (n := n) (X := X) (Y := Y) S - sumXY (n := n) (X := X) (Y := Y) S'| / D := this
        _ ≤ |sumXY (n := n) (X := X) (Y := Y) S - sumXY (n := n) (X := X) (Y := Y) S'|
              / (lam * N (n := n)) := by
              exact div_le_div_of_nonneg_left h0 hlamNpos hDge
        _ ≤ (2 * X * Y) / (lam * N (n := n)) := by
              exact div_le_div_of_nonneg_right hBdiff (le_of_lt hlamNpos)
    have hterm2 :
        |sumXY (n := n) (X := X) (Y := Y) S'| * |(1 / D) - (1 / D')|
          ≤ (2 * X ^ 3 * Y) / (lam ^ 2 * N (n := n)) := by
      have hN0 : 0 ≤ N (n := n) := le_of_lt (N_pos (n := n))
      have hB0 : 0 ≤ N (n := n) * X * Y := mul_nonneg (mul_nonneg hN0 z.X_nonneg) z.Y_nonneg
      have hMul :
          |sumXY (n := n) (X := X) (Y := Y) S'| * |(1 / D) - (1 / D')|
            ≤ (N (n := n) * X * Y) * ((2 * X ^ 2) / (lam ^ 2 * (N (n := n)) ^ 2)) := by
        exact mul_le_mul hB' hInv (abs_nonneg _) hB0
      have hNne : (N (n := n)) ≠ 0 := ne_of_gt (N_pos (n := n))
      have hSimp :
          (N (n := n) * X * Y) * ((2 * X ^ 2) / (lam ^ 2 * (N (n := n)) ^ 2))
            = (2 * X ^ 3 * Y) / (lam ^ 2 * N (n := n)) := by
        field_simp [hNne]
      simpa [hSimp] using hMul
    have hsplit :
        |(sumXY (n := n) (X := X) (Y := Y) S) / D - (sumXY (n := n) (X := X) (Y := Y) S') / D'|
          ≤ (2 * X * Y) / (lam * N (n := n)) + (2 * X ^ 3 * Y) / (lam ^ 2 * N (n := n)) := by
      have htri :=
        abs_sub_le ((sumXY (n := n) (X := X) (Y := Y) S) / D)
          ((sumXY (n := n) (X := X) (Y := Y) S') / D)
          ((sumXY (n := n) (X := X) (Y := Y) S') / D')
      have h1 :
          |(sumXY (n := n) (X := X) (Y := Y) S) / D - (sumXY (n := n) (X := X) (Y := Y) S') / D|
            = |(sumXY (n := n) (X := X) (Y := Y) S - sumXY (n := n) (X := X) (Y := Y) S') / D| := by
              ring_nf
      have h2 :
          |(sumXY (n := n) (X := X) (Y := Y) S') / D - (sumXY (n := n) (X := X) (Y := Y) S') / D'|
            = |sumXY (n := n) (X := X) (Y := Y) S'| * |(1 / D) - (1 / D')| := by
        have hEq :
            (sumXY (n := n) (X := X) (Y := Y) S') / D - (sumXY (n := n) (X := X) (Y := Y) S') / D'
              = (sumXY (n := n) (X := X) (Y := Y) S') * ((1 / D) - (1 / D')) := by
          simp [div_eq_mul_inv]
          ring_nf
        calc
          |(sumXY (n := n) (X := X) (Y := Y) S') / D - (sumXY (n := n) (X := X) (Y := Y) S') / D'|
              = |(sumXY (n := n) (X := X) (Y := Y) S') * ((1 / D) - (1 / D'))| := by
                  simp [hEq]
          _ = |sumXY (n := n) (X := X) (Y := Y) S'| * |(1 / D) - (1 / D')| := by simp [abs_mul]
      have htri' :
          |(sumXY (n := n) (X := X) (Y := Y) S) / D - (sumXY (n := n) (X := X) (Y := Y) S') / D'|
            ≤ |(sumXY (n := n) (X := X) (Y := Y) S - sumXY (n := n) (X := X) (Y := Y) S') / D|
              + (|sumXY (n := n) (X := X) (Y := Y) S'| * |(1 / D) - (1 / D')|) := by
              simpa [h1, h2] using htri
      nlinarith [htri', hterm1, hterm2]
    have hw_eq :
        |w - w'| =
          |(sumXY (n := n) (X := X) (Y := Y) S) / D -
            (sumXY (n := n) (X := X) (Y := Y) S') / D'| := by
      simp [w, w', hw_def, hw'_def]
    have hsimp :
        (2 * X * Y) / (lam * N (n := n)) + (2 * X ^ 3 * Y) / (lam ^ 2 * N (n := n))
          = (2 * X * Y * (lam + X ^ 2)) / (lam ^ 2 * N (n := n)) := by
      have hNne : (N (n := n)) ≠ 0 := ne_of_gt (N_pos (n := n))
      field_simp [hNne, (ne_of_gt hlam)]
    calc
      |w - w'|
          = |(sumXY (n := n) (X := X) (Y := Y) S) / D - (sumXY (n := n) (X := X) (Y := Y) S') / D'|
            := hw_eq
      _ ≤ (2 * X * Y) / (lam * N (n := n)) + (2 * X ^ 3 * Y) / (lam ^ 2 * N (n := n)) := hsplit
      _ = (2 * X * Y * (lam + X ^ 2)) / (lam ^ 2 * N (n := n)) := hsimp
  -- Convert `|w-w'|` to a loss difference bound.
  set e : ℝ := w * z.x - z.y
  set e' : ℝ := w' * z.x - z.y
  have hres : |e| ≤ Y * (lam + X ^ 2) / lam := by
    simpa [e, w] using abs_residual_le (n := n) (X := X) (Y := Y) (lam := lam) hlam S z
  have hres' : |e'| ≤ Y * (lam + X ^ 2) / lam := by
    simpa [e', w', S'] using abs_residual_le (n := n) (X := X) (Y := Y) (lam := lam) hlam S' z
  have hx : |z.x| ≤ X := z.abs_x_le
  have he_diff : |e - e'| ≤ X * |w - w'| := by
    have : e - e' = (w - w') * z.x := by
      simp [e, e', sub_eq_add_neg]
      ring_nf
    calc
      |e - e'| = |(w - w') * z.x| := by simp [this]
      _ = |w - w'| * |z.x| := by simp [abs_mul]
      _ ≤ |w - w'| * X := by
            exact mul_le_mul_of_nonneg_left hx (abs_nonneg (w - w'))
      _ = X * |w - w'| := by ring
  have he_sum : |e + e'| ≤ 2 * (Y * (lam + X ^ 2) / lam) := by
    have : |e + e'| ≤ |e| + |e'| := by simpa using abs_add_le e e'
    nlinarith [this, hres, hres']
  have hloss :
      |sqLoss (X := X) (Y := Y) w z - sqLoss (X := X) (Y := Y) w' z|
        = |e - e'| * |e + e'| := by
    have hEq : sqLoss (X := X) (Y := Y) w z - sqLoss (X := X) (Y := Y) w' z = (e - e') * (e + e') :=
      by
      simp [sqLoss, e, e', pow_two]
      ring_nf
    calc
      |sqLoss (X := X) (Y := Y) w z - sqLoss (X := X) (Y := Y) w' z|
          = |(e - e') * (e + e')| := by simp [hEq]
      _ = |e - e'| * |e + e'| := by simp [abs_mul]
  calc
    |sqLoss (X := X) (Y := Y) w z - sqLoss (X := X) (Y := Y) w' z|
        = |e - e'| * |e + e'| := hloss
    _ ≤ (X * |w - w'|) * (2 * (Y * (lam + X ^ 2) / lam)) := by
          have hBw0 : 0 ≤ X * |w - w'| := mul_nonneg z.X_nonneg (abs_nonneg _)
          exact mul_le_mul he_diff he_sum (abs_nonneg _) hBw0
    _ ≤ (X * ((2 * X * Y * (lam + X ^ 2)) / (lam ^ 2 * N (n := n))))
          * (2 * (Y * (lam + X ^ 2) / lam)) := by
            have hC0 : 0 ≤ 2 * (Y * (lam + X ^ 2) / lam) := by
              have : 0 ≤ Y * (lam + X ^ 2) / lam :=
                div_nonneg (mul_nonneg z.Y_nonneg (add_nonneg hlam.le (sq_nonneg X)))
                  (le_of_lt hlam)
              nlinarith
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw_diff z.X_nonneg) hC0
    _ = 4 * X ^ 2 * Y ^ 2 * (lam + X ^ 2) ^ 2 / (lam ^ 3 * N (n := n)) := by
          have hNne : (N (n := n)) ≠ 0 := ne_of_gt (N_pos (n := n))
          field_simp [hNne, (ne_of_gt hlam)]
          ring_nf

end Ridge1D

end LeanLearn.LearningTheory.Stability.RidgeRegression1D
