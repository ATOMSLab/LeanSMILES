/-
Copyright (c) 2026 TorchLean
Released under MIT license as described in the file LICENSES/TorchLean-MIT.txt.
Authors: TorchLean Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Gradient Descent: Linear Convergence from Strong Monotonicity + Lipschitz Gradient

This module proves a linear convergence bound for the iteration

$$
x_{k+1}=x_k-\eta g(x_k)
$$

under two assumptions on `g` over a real inner product space:

1. $g$ is **$\mu$-strongly monotone**:
   $\mu\lVert x-y\rVert^2 \leq \langle x-y, g(x)-g(y)\rangle$.
2. $g$ is **$L$-Lipschitz**:
   $\lVert g(x)-g(y)\rVert \leq L\lVert x-y\rVert$.

For gradients of $\mu$-strongly convex and $L$-smooth functions, these are the standard
operator-level properties that imply linear convergence of gradient descent with a suitable step
size.

This module avoids any heavy Fréchet-derivative setup: it is stated directly in terms
of $g$ so it can later be instantiated either by $g=\nabla f$ theorems or by verified gradients of
concrete TorchLean models.

## Provenance

Extracted from TorchLean (`NN/MLTheory/Optimization/GDLinearConvergence.lean`, `main` at `772b6b8`),
MIT-licensed; see `LICENSES/TorchLean-MIT.txt`. The code is unchanged apart from the `LeanSMILES`
namespace and import paths.
-/

@[expose] public section

namespace LeanLearn
namespace Optim
namespace GD

open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Strong monotonicity of an operator in a real inner product space. -/
def StrongMonotone (μ : ℝ) (g : E → E) : Prop :=
  ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪x - y, g x - g y⟫

/-- One gradient-descent-like step for an operator `g`. -/
def step (η : ℝ) (g : E → E) (x : E) : E :=
  x - η • g x

/-- Expand the difference of two `step` applications. -/
theorem step_sub_step (η : ℝ) (g : E → E) (x y : E) :
    step η g x - step η g y = (x - y) - η • (g x - g y) := by
  simp [step, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/--
Key contraction-in-squared-norm inequality.

If $g$ is $\mu$-strongly monotone and $L$-Lipschitz, then
$$
\lVert \operatorname{step}_\eta(g,x)-\operatorname{step}_\eta(g,y)\rVert^2
  \leq q\lVert x-y\rVert^2,
\qquad
q=1-2\eta\mu+\eta^2L^2.
$$
-/
theorem step_norm_sq_le (η μ : ℝ) (hη : 0 ≤ η) {L : NNReal} (g : E → E)
    (hmono : StrongMonotone μ g) (hlip : LipschitzWith L g)
    (x y : E) :
    ‖step η g x - step η g y‖ ^ 2 ≤ (1 - 2 * η * μ + (η ^ 2) * (L : ℝ) ^ 2) * ‖x - y‖ ^ 2 := by
  have hxy : step η g x - step η g y = (x - y) - η • (g x - g y) := step_sub_step η g x y
  have hL : ‖g x - g y‖ ≤ (L : ℝ) * ‖x - y‖ := by
    simpa [dist_eq_norm] using hlip.dist_le_mul x y
  have hμ : μ * ‖x - y‖ ^ 2 ≤ ⟪x - y, g x - g y⟫ := hmono x y
  -- Expand `‖(x - y) - η • (g x - g y)‖ ^ 2` and rewrite the mixed and scaled terms.
  have hExp :
      ‖(x - y) - η • (g x - g y)‖ ^ 2 =
        ‖x - y‖ ^ 2 - 2 * ⟪x - y, η • (g x - g y)⟫ + ‖η • (g x - g y)‖ ^ 2 := by
    simpa using (norm_sub_sq_real (x := (x - y)) (y := (η • (g x - g y))))
  have hInner : ⟪x - y, η • (g x - g y)⟫ = η * ⟪x - y, g x - g y⟫ := by
    simpa using (real_inner_smul_right (x := x - y) (y := g x - g y) η)
  have hNormSmul : ‖η • (g x - g y)‖ ^ 2 = (η ^ 2) * ‖g x - g y‖ ^ 2 := by
    -- `‖η • v‖ = |η| ‖v‖`, and `η ≥ 0` removes the absolute value.
    simp [norm_smul, Real.norm_eq_abs, pow_two, abs_of_nonneg hη, mul_assoc, mul_left_comm,
      mul_comm]
  have hstep :
      ‖step η g x - step η g y‖ ^ 2
        = ‖x - y‖ ^ 2 - 2 * (η * ⟪x - y, g x - g y⟫) + (η ^ 2) * ‖g x - g y‖ ^ 2 := by
    calc
      ‖step η g x - step η g y‖ ^ 2
          = ‖(x - y) - η • (g x - g y)‖ ^ 2 := by simp [hxy]
      _ = ‖x - y‖ ^ 2 - 2 * ⟪x - y, η • (g x - g y)⟫ + ‖η • (g x - g y)‖ ^ 2 := by
            simpa using hExp
      _ = ‖x - y‖ ^ 2 - 2 * (η * ⟪x - y, g x - g y⟫) + (η ^ 2) * ‖g x - g y‖ ^ 2 := by
            simp [hInner, hNormSmul, mul_assoc, mul_comm]
  -- Strong monotonicity tightens the mixed term (this is where `η ≥ 0` is used) and the squared
  -- Lipschitz bound controls the last term.
  have hInnerBound : -2 * (η * ⟪x - y, g x - g y⟫) ≤ -2 * (η * (μ * ‖x - y‖ ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hμ hη
    linarith
  have hL2 : ‖g x - g y‖ ^ 2 ≤ (L : ℝ) ^ 2 * ‖x - y‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hL 2
  have hLastBound :
      (η ^ 2) * ‖g x - g y‖ ^ 2 ≤ (η ^ 2) * ((L : ℝ) ^ 2 * ‖x - y‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hL2 (sq_nonneg η)
  calc
    ‖step η g x - step η g y‖ ^ 2
        ≤ ‖x - y‖ ^ 2 - 2 * (η * (μ * ‖x - y‖ ^ 2)) + (η ^ 2) * ((L : ℝ) ^ 2 * ‖x - y‖ ^ 2) := by
          linarith [hstep, hInnerBound, hLastBound]
    _ = (1 - 2 * η * μ + (η ^ 2) * (L : ℝ) ^ 2) * ‖x - y‖ ^ 2 := by ring

end GD
end Optim
end LeanLearn
