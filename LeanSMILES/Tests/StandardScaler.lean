import LeanSMILES.API.Features
import LeanSMILES.MetaPrograms.Test

/-! Tests for `StandardScaler`. -/

open Primitives ML API

def close (a b : Float) (tol : Float := 1e-12) : Bool := (a - b).abs < tol

def X : Mat Float 4 2 := #v[#v[0.0, 5.0], #v[2.0, 5.0], #v[4.0, 5.0], #v[6.0, 5.0]]
def sc := StandardScaler.fit X

#test sc.mean.toList == [3.0, 5.0]
-- population std of 0, 2, 4, 6 is √5; a constant column gets scale 1
#test close sc.scale[0] (5.0 : Float).sqrt && sc.scale[1] == 1.0
-- transformed columns have mean 0 and (population) variance 1
#test let Z := sc.transform X
  close (colMean Z)[0] 0.0 && close (colMean Z)[1] 0.0 &&
    close ((List.finRange 4).foldl (fun a i => a + Z[i][0] * Z[i][0]) 0 / 4) 1.0
#test (sc.transformVec #v[3.0, 5.0]).toList == [0.0, 0.0]
