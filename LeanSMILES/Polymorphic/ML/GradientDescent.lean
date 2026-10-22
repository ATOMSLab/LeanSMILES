module

public import LeanSMILES.Polymorphic.ML.Types

/-!
# Machine Learning — Gradient descent

Gradient descent on an `Objective` with a constant step size. Least squares
(`LeastSquares.lean`) runs it on the mean squared error.
-/

@[expose] public section

namespace ML

open Primitives

section GradientDescent

variable {α : Type} [Scalar α] {n : Nat}

/-- One step `w ↦ w - η ∇f(w)`. Entrywise:
`(gdStep obj η w)[i] = w[i] - η * (obj.grad w)[i]` (`gdStep_getElem` in
`Proofs/ML/Basic.lean`). -/
@[specialize] def gdStep (obj : Objective α n) (η : α) (w : Vec α n) : Vec α n :=
  vsub w (smul η (obj.grad w))

/-- `cfg.iters` steps of gradient descent from `w₀`, i.e. `iterate (gdStep obj η) k w₀`,
so proofs can induct on `k` with `gradientDescent_succ`.
For `η ≠ 0` its fixed points are exactly the zeros of `obj.grad` (`gdStep_eq_self_iff` in
`Proofs/ML/LeastSquares.lean`); for least squares the `O(1/k)` rate is
`mse_linRegGD_le` in `Proofs/ML/Convergence.lean`. -/
@[specialize] def gradientDescent (obj : Objective α n) (cfg : GDConfig α) (w₀ : Vec α n) :
    Vec α n :=
  iterate (gdStep obj cfg.stepSize) cfg.iters w₀

/-- One step of `gradientDescentWithHistory`: a `gdStep`, then record `(k, loss)` every
`every` iterations. -/
@[specialize] def gdHistoryStep (obj : Objective α n) (η : α) (every : Nat)
    (state : Vec α n × Nat × Array (Nat × α)) : Vec α n × Nat × Array (Nat × α) :=
  let (w, k, hist) := state
  let w' := gdStep obj η w
  (w', k + 1, if (k + 1) % every == 0 then hist.push (k + 1, obj.loss w') else hist)

/-- `gradientDescent` that also records the loss at iteration 0 and every `every`
iterations (for training curves). The first component is `gradientDescent obj cfg w₀`
(`gradientDescentWithHistory_fst` in `Proofs/ML/Basic.lean`). -/
@[specialize] def gradientDescentWithHistory (obj : Objective α n) (cfg : GDConfig α)
    (w₀ : Vec α n) (every : Nat := 1) : Vec α n × Array (Nat × α) :=
  let (w, _, hist) := iterate (gdHistoryStep obj cfg.stepSize every) cfg.iters
    (w₀, 0, #[(0, obj.loss w₀)])
  (w, hist)

end GradientDescent

end ML

end
