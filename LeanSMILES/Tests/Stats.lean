import LeanSMILES.API.Stats
import LeanSMILES.MetaPrograms.Test

/-! Tests for `describe`, `histogram` and `formatFloat`. -/

open Primitives API

def close (a b : Float) (tol : Float := 1e-12) : Bool := (a - b).abs < tol

def v : Vec Float 5 := #v[1.0, 2.0, 3.0, 4.0, 10.0]

#test (describe v).count == 5
#test (describe v).mean == 4.0
#test (describe v).min == 1.0 && (describe v).max == 10.0
-- sample standard deviation (ddof = 1): √(50 / 4)
#test close (describe v).std (12.5 : Float).sqrt
-- every value lands in a bin, the maximum in the last one
#test ((histogram v 3).map (·.2.2)).toList == [3, 1, 1]
#test ((histogram v 4).toList.map (·.2.2)).foldl (· + ·) 0 == 5

#test formatFloat 3.14159 == "3.14"
#test formatFloat (-2.005) 1 == "-2.0"
#test formatFloat 0.5 3 == "0.500"
#test formatFloat (-0.001) == "0.00"
#test formatFloat 12.0 0 == "12"
