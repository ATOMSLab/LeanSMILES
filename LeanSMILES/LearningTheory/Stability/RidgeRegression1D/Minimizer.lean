module

public import LeanSMILES.LearningTheory.Stability.RidgeRegression1D.Real

/-!
# 1D ridge regression: the closed form is the unique minimizer

`RidgeRegression1D.Real` defines

$$
\operatorname{ridgeFit1D}(\lambda,S)=\frac{\sum_i x_i y_i}{\sum_i x_i^2+\lambda N}
$$

and proves it uniformly stable, but takes on trust that this ratio *is* the ridge estimator. This
file discharges that: for $\lambda>0$, `ridgeFit1D λ S` is the unique minimizer over $\mathbb R$ of
the regularized empirical risk

$$
J(w)=\frac1N\sum_i(wx_i-y_i)^2+\lambda w^2 ,
$$

stated with `Stability.Core`'s `empiricalError` of the file's own `sqLoss`.

## Proof idea

Completing the square; no calculus. Writing $A=\sum_i x_i^2$, $B=\sum_i x_iy_i$,
$C=\sum_i y_i^2$ and $D=A+\lambda N>0$,

$$
J(w)=\frac{Dw^2-2Bw+C}{N}=J(\widehat w)+\frac DN\,(w-\widehat w)^2,
\qquad \widehat w=\frac BD,
$$

so $J(w)\ge J(\widehat w)$, with equality only at $w=\widehat w$.

## Main results

* `Ridge1D.ridgeObjective_eq_add_sq`: the completed-square identity.
* `Ridge1D.ridgeFit1D_isMinOn`: `ridgeFit1D λ S` minimizes `ridgeObjective λ S` over `ℝ`.
* `Ridge1D.eq_ridgeFit1D_of_le`: any `w` doing at least as well equals `ridgeFit1D λ S`.
* `Ridge1D.isMinOn_univ_iff_eq_ridgeFit1D`: `w` minimizes the objective iff `w = ridgeFit1D λ S`
  (existence and uniqueness in one statement).
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LeanSMILES.LearningTheory.Stability.RidgeRegression1D

variable {n : Nat} {X Y : ℝ}

/-- Sum of squared labels $\sum_i y_i^2$. -/
def sumYY (S : Dataset (n + 1) (BoundedExample X Y)) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), (Dataset.get S i).y ^ 2

/--
The 1D ridge objective $J(w)=\frac1N\sum_i(wx_i-y_i)^2+\lambda w^2$: the empirical squared loss
of the hypothesis `w` on `S`, plus the penalty $\lambda w^2$.
-/
def ridgeObjective (lam : ℝ) (S : Dataset (n + 1) (BoundedExample X Y)) (w : ℝ) : ℝ :=
  empiricalError (fun w z => sqLoss (X := X) (Y := Y) w z) w S + lam * w ^ 2

namespace Ridge1D

variable {lam : ℝ}

/-- The summed squared loss is the quadratic $w^2A-2wB+C$ in the three data sums. -/
theorem sum_sqLoss_eq (S : Dataset (n + 1) (BoundedExample X Y)) (w : ℝ) :
    ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), sqLoss (X := X) (Y := Y) w (Dataset.get S i) =
      w ^ 2 * sumXX (n := n) S - 2 * w * sumXY (n := n) S + sumYY (n := n) S := by
  rw [sumXX, sumXY, sumYY, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sqLoss]
  ring

/-- The ridge objective as one quadratic over $N$: $J(w)=(Dw^2-2Bw+C)/N$ with
$D=A+\lambda N$. -/
theorem ridgeObjective_eq_quadratic (S : Dataset (n + 1) (BoundedExample X Y)) (w : ℝ) :
    ridgeObjective lam S w =
      ((sumXX (n := n) S + lam * N (n := n)) * w ^ 2 - 2 * sumXY (n := n) S * w
        + sumYY (n := n) S) / N (n := n) := by
  have hN : N (n := n) ≠ 0 := ne_of_gt (N_pos (n := n))
  have hsum := sum_sqLoss_eq (n := n) (X := X) (Y := Y) S w
  rw [ridgeObjective, empiricalError, hsum]
  change (1 / N (n := n)) * _ + _ = _
  field_simp
  ring

/-- The ridge denominator $D=\sum_i x_i^2+\lambda N$ is positive when $\lambda>0$. -/
theorem ridgeDenom_pos (hlam : 0 < lam) (S : Dataset (n + 1) (BoundedExample X Y)) :
    0 < sumXX (n := n) S + lam * N (n := n) := by
  have hA : 0 ≤ sumXX (n := n) S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlamN : 0 < lam * N (n := n) := mul_pos hlam (N_pos (n := n))
  linarith

/--
**Completed square.** For $\lambda>0$,
$J(w)=J(\widehat w)+\frac DN(w-\widehat w)^2$ with $\widehat w=$ `ridgeFit1D λ S`.
-/
theorem ridgeObjective_eq_add_sq (hlam : 0 < lam) (S : Dataset (n + 1) (BoundedExample X Y))
    (w : ℝ) :
    ridgeObjective lam S w =
      ridgeObjective lam S (ridgeFit1D (n := n) lam S)
        + (sumXX (n := n) S + lam * N (n := n)) / N (n := n)
          * (w - ridgeFit1D (n := n) lam S) ^ 2 := by
  have hD : sumXX (n := n) S + lam * N (n := n) ≠ 0 := ne_of_gt (ridgeDenom_pos hlam S)
  have hN : N (n := n) ≠ 0 := ne_of_gt (N_pos (n := n))
  have hfit : ridgeFit1D (n := n) lam S =
      sumXY (n := n) S / (sumXX (n := n) S + lam * N (n := n)) := rfl
  rw [ridgeObjective_eq_quadratic, ridgeObjective_eq_quadratic, hfit]
  field_simp
  ring

/-- **Existence.** For $\lambda>0$, `ridgeFit1D λ S` minimizes the ridge objective over `ℝ`. -/
theorem ridgeFit1D_isMinOn (hlam : 0 < lam) (S : Dataset (n + 1) (BoundedExample X Y)) :
    IsMinOn (ridgeObjective lam S) Set.univ (ridgeFit1D (n := n) lam S) := by
  rw [isMinOn_univ_iff]
  intro w
  have hc : 0 ≤ (sumXX (n := n) S + lam * N (n := n)) / N (n := n) :=
    div_nonneg (ridgeDenom_pos hlam S).le (N_pos (n := n)).le
  have hsq := mul_nonneg hc (sq_nonneg (w - ridgeFit1D (n := n) lam S))
  rw [ridgeObjective_eq_add_sq hlam S w]
  linarith

/-- **Uniqueness.** For $\lambda>0$, any `w` whose objective is at most that of
`ridgeFit1D λ S` is `ridgeFit1D λ S`. -/
theorem eq_ridgeFit1D_of_le (hlam : 0 < lam) (S : Dataset (n + 1) (BoundedExample X Y))
    {w : ℝ} (h : ridgeObjective lam S w ≤ ridgeObjective lam S (ridgeFit1D (n := n) lam S)) :
    w = ridgeFit1D (n := n) lam S := by
  have hc : 0 < (sumXX (n := n) S + lam * N (n := n)) / N (n := n) :=
    div_pos (ridgeDenom_pos hlam S) (N_pos (n := n))
  rw [ridgeObjective_eq_add_sq hlam S w] at h
  have hle : (sumXX (n := n) S + lam * N (n := n)) / N (n := n)
      * (w - ridgeFit1D (n := n) lam S) ^ 2
      ≤ (sumXX (n := n) S + lam * N (n := n)) / N (n := n) * 0 := by
    rw [mul_zero]
    linarith
  have hsq : (w - ridgeFit1D (n := n) lam S) ^ 2 = 0 :=
    le_antisymm (le_of_mul_le_mul_left hle hc) (sq_nonneg _)
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)

/--
**The closed form is the ridge estimator.** For $\lambda>0$, `w` minimizes
$J(w)=\frac1N\sum_i(wx_i-y_i)^2+\lambda w^2$ over `ℝ` if and only if `w = ridgeFit1D λ S`.
-/
theorem isMinOn_univ_iff_eq_ridgeFit1D (hlam : 0 < lam)
    (S : Dataset (n + 1) (BoundedExample X Y)) (w : ℝ) :
    IsMinOn (ridgeObjective lam S) Set.univ w ↔ w = ridgeFit1D (n := n) lam S := by
  constructor
  · intro h
    exact eq_ridgeFit1D_of_le hlam S (isMinOn_univ_iff.mp h _)
  · rintro rfl
    exact ridgeFit1D_isMinOn hlam S

end Ridge1D

end LeanSMILES.LearningTheory.Stability.RidgeRegression1D
