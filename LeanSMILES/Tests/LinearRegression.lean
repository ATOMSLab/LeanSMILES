import LeanSMILES.MachineLearning.Definitions
import LeanSMILES.MetaPrograms.Test

/-! Tests for linear regression (`olsFit`, `linRegGD`, `mse`) and parameter packing. -/

open Primitives ML

def close (a b : Float) (tol : Float := 1e-6) : Bool := (a - b).abs < tol

-- noiseless data from y = 2·x₀ - 3·x₁ + 1
def X : Mat Float 5 2 :=
  #v[#v[0.0, 0.0], #v[1.0, 0.0], #v[0.0, 1.0], #v[2.0, 3.0], #v[-1.0, 4.0]]
def data : Dataset Float 5 2 :=
  { X := X, y := Vector.ofFn fun i => 2.0 * X[i][0] - 3.0 * X[i][1] + 1.0 }

def ols := olsFit data
#test close ols.weights[0] 2.0 && close ols.weights[1] (-3.0) && close ols.bias 1.0
#test mse ols data < 1e-20

def gd := linRegGD ⟨0.02, 20000⟩ data
#test close gd.weights[0] 2.0 && close gd.weights[1] (-3.0) && close gd.bias 1.0

-- the zero model's MSE is the mean of y²
#test close (mse LinearModel.zero data) ((data.y.toList.map (· ^ 2)).foldl (· + ·) 0 / 5)
-- packing round trip
#test (LinearModel.ofParams (n := 2) ols.toParams).weights.toList == ols.weights.toList
#test (LinearModel.ofParams (n := 2) ols.toParams).bias == ols.bias
-- predictAll agrees with score
#test (List.finRange 5).all fun i => (ols.predictAll data.X)[i] == ols.score data.X[i]
