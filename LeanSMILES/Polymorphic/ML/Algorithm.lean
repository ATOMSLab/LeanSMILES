module

public import LeanSMILES.Polymorphic.ML.LeastSquares
public import LeanSMILES.Polymorphic.ML.Perceptron

/-!
# Machine Learning — Algorithms

The learning algorithms a pipeline can be configured with, as data: the algorithm and its
hyperparameters. `Algorithm.fit` trains it. Because the choice is a value, a theorem can
case on it, and `Proofs/Pipeline.lean` gives each algorithm its guarantee.
-/

@[expose] public section

namespace ML

open Primitives

/-- A learning algorithm with its hyperparameters. Every one of them trains a
`LinearModel`. -/
inductive Algorithm (α : Type) where
  /-- Closed-form least squares: solve the normal equations (`olsFit`). -/
  | ols
  /-- Least squares by gradient descent from `θ = 0`. It runs `linRegGDSparse`, which
  computes the same iterates as `linRegGD` (`linRegGDSparse_eq`). -/
  | gradientDescent (cfg : GDConfig α)
  /-- The perceptron, for `±1` labels (`perceptronFit`). -/
  | perceptron (cfg : PerceptronConfig α)

namespace Algorithm

variable {α : Type} [Scalar α] {m n : Nat}

/-- Train the algorithm on a dataset. -/
@[specialize] def fit : Algorithm α → Dataset α m n → LinearModel α n
  | .ols, data => olsFit data
  | .gradientDescent cfg, data => linRegGDSparse cfg data
  | .perceptron cfg, data => perceptronFit cfg data

/-- Whether the algorithm fits real-valued targets (regression) or `±1` labels. -/
def isClassifier : Algorithm α → Bool
  | .perceptron _ => true
  | _ => false

end Algorithm

end ML

end
