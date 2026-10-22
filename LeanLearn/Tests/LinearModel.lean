module

public import LeanLearn.Regression.LinearModel

/-!
# Executable Float checks for the shared regression definitions

These are small numerical checks of predictions and objectives, not a training
or evaluation pipeline. The coefficients are supplied explicitly. The general
optimality proofs are in `OLS.lean`, `Ridge.lean`, and `LinearModel.lean`.

Run: `lake exe linear-model-test`
-/
namespace LeanLearn.Tests.LinearModel
open Matrix
open scoped Matrix
open LeanLearn.Regression.LinearModel

def X : Design Float 3 2 := !![1, 0; 1, 1; 1, 2]
def y : Fin 3 → Float := ![1, 3, 5]

private def near (actual expected : Float) : IO Unit :=
  unless actual.isFinite && (actual - expected).abs ≤ 1e-10 * (1 + expected.abs) do
    throw (IO.userError s!"expected {expected}, received {actual}")

def run : IO Unit := do
  let ols : Fin 2 → Float := ![1, 2]
  let ridge : Fin 2 → Float := ![2, 1]
  let weights : Fin 2 → Float := ![0, 2]
  near (predictRow ![1, 3] ols) 7
  near (predictRow ![1, 3] ridge) 5
  near (squaredError X y ols) 0
  near (squaredError X y ridge) 2
  near (penalty weights ridge) 2
  near (ridgeLoss X y weights ridge) 4
  let g := normalResidual X y weights ridge
  near (g 0) 0
  near (g 1) 0
  IO.println s!"OLS predictions: {Array.ofFn (predict X ols)}"
  IO.println s!"Ridge predictions: {Array.ofFn (predict X ridge)}"
  IO.println s!"Ridge squared error: {squaredError X y ridge}"
  IO.println s!"Ridge objective: {ridgeLoss X y weights ridge}"
  IO.println "8/8 Float definition checks passed"

end LeanLearn.Tests.LinearModel
public def main : IO Unit := LeanLearn.Tests.LinearModel.run
