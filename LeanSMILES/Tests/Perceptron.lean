import LeanSMILES.MachineLearning.Definitions
import LeanSMILES.MetaPrograms.Test

/-! Tests for the perceptron (`perceptronStep`, `perceptronEpoch`, `perceptronFit`). -/

open Primitives ML

-- linearly separable: label = sign(x₀ - x₁)
def data : Dataset Float 4 2 :=
  { X := #v[#v[2.0, 1.0], #v[1.0, 3.0], #v[3.0, 0.5], #v[0.0, 2.0]]
    y := #v[1.0, -1.0, 1.0, -1.0] }

def fit := perceptronFit ⟨1.0, 10⟩ data

#test (List.finRange 4).all fun i => fit.classify data.X[i] == data.y[i]
#test (List.finRange 4).all fun i => perceptronLoss fit data.X[i] data.y[i] == 0.0
-- the zero model misclassifies everything (score 0 is on the boundary), so it updates
#test (perceptronStep 1.0 LinearModel.zero #v[2.0, 1.0] 1.0).weights.toList == [2.0, 1.0]
-- a correctly classified sample leaves the model unchanged
#test (perceptronStep 1.0 fit data.X[0] data.y[0]).weights.toList == fit.weights.toList
-- once converged, further epochs change nothing
#test (perceptronEpoch 1.0 data fit).weights.toList == fit.weights.toList
-- 100000 epochs stay fast
#test (perceptronFit ⟨1.0, 100000⟩ data).bias == fit.bias
