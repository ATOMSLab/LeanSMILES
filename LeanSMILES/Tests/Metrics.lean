import LeanSMILES.API.Metrics
import LeanSMILES.MetaPrograms.Test

/-! Tests for `meanSquaredError`, `rootMeanSquaredError`, `meanAbsoluteError`, `r2Score`
and `evaluate`. -/

open Primitives ML API

def close (a b : Float) (tol : Float := 1e-12) : Bool := (a - b).abs < tol

def yTrue : Vec Float 4 := #v[3.0, -0.5, 2.0, 7.0]
def yPred : Vec Float 4 := #v[2.5, 0.0, 2.0, 8.0]

-- the example values from the scikit-learn documentation
#test close (meanSquaredError yTrue yPred) 0.375
#test close (rootMeanSquaredError yTrue yPred) 0.375.sqrt
#test close (meanAbsoluteError yTrue yPred) 0.5
#test close (r2Score yTrue yPred) 0.9486081370449679
-- perfect predictions
#test r2Score yTrue yTrue == 1.0 && meanSquaredError yTrue yTrue == 0.0
-- predicting the mean scores 0
#test close (r2Score yTrue (Vector.replicate 4 2.875)) 0.0
-- constant target
#test r2Score (Vector.replicate 3 1.0) (Vector.replicate 3 1.0) == 1.0
#test r2Score (Vector.replicate 3 1.0) #v[1.0, 2.0, 1.0] == 0.0

-- `evaluate` uses the model's predictions
def model : LinearModel Float 1 := { weights := #v[2.0], bias := 1.0 }
def data : Dataset Float 3 1 := { X := #v[#v[0.0], #v[1.0], #v[2.0]], y := #v[1.0, 3.0, 6.0] }
#test close (evaluate model data).mse (1.0 / 3.0)
#test close (evaluate model data).mae (1.0 / 3.0)
