import LeanSMILES.Primitives.LinAlg
import LeanSMILES.MetaPrograms.Test

/-! Tests for `Primitives/LinAlg.lean`: vector and matrix operations and `linSolve`. -/

open Primitives

def close (a b : Float) (tol : Float := 1e-9) : Bool := (a - b).abs < tol
def closeVec {n : Nat} (u v : Vec Float n) (tol : Float := 1e-9) : Bool :=
  (List.finRange n).all fun i => close u[i] v[i] tol

#test dot (α := Float) #v[1.0, 2.0, 3.0] #v[4.0, 5.0, 6.0] == 32.0
#test norm (α := Float) #v[3.0, 4.0] == 5.0
#test distSq (α := Float) #v[1.0, 1.0] #v[4.0, 5.0] == 25.0
#test vsum (α := Float) #v[1.0, 2.0, 3.5] == 6.5
#test (vadd (α := Float) #v[1.0, 2.0] #v[3.0, 4.0]).toList == [4.0, 6.0]
#test (smul (α := Float) 2.0 #v[1.0, -2.0]).toList == [2.0, -4.0]

def A : Mat Float 2 3 := #v[#v[1.0, 2.0, 3.0], #v[4.0, 5.0, 6.0]]

#test (matVec A #v[1.0, 0.0, -1.0]).toList == [-2.0, -2.0]
#test ((transpose A).map (·.toList)).toList == [[1.0, 4.0], [2.0, 5.0], [3.0, 6.0]]
#test ((matMul A (transpose A)).map (·.toList)).toList == [[14.0, 32.0], [32.0, 77.0]]
#test ((gram A).map (·.toList)).toList[0]! == [17.0, 22.0, 27.0]
#test (augment (α := Float) #v[7.0, 8.0]).toList == [7.0, 8.0, 1.0]
#test (colMean A).toList == [2.5, 3.5, 4.5]
#test ((center A).map (·.toList)).toList == [[-1.5, -1.5, -1.5], [1.5, 1.5, 1.5]]

-- `linSolve`: the top-left pivot is zero, so a row swap is needed. Solution (5, 3, -1).
def M : Mat Float 3 3 := #v[#v[0.0, 1.0, 2.0], #v[1.0, 0.0, 3.0], #v[4.0, -3.0, 8.0]]
def b : Vec Float 3 := #v[1.0, 2.0, 3.0]

#test closeVec (linSolve M b) #v[5.0, 3.0, -1.0]
#test closeVec (matVec M (linSolve M b)) b
#test closeVec (linSolve (identity (α := Float) (n := 3)) b) b
