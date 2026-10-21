import LeanSMILES.MachineLearning.Definitions
import LeanSMILES.MetaPrograms.Test

/-! Tests for `gdStep` and `gradientDescent`. -/

open Primitives ML

def close (a b : Float) (tol : Float := 1e-6) : Bool := (a - b).abs < tol

-- f(w) = ‖w - c‖², ∇f(w) = 2(w - c), minimised at c.
def c : Vec Float 3 := #v[1.0, -2.0, 3.0]
def quad : Objective Float 3 :=
  { loss := fun w => distSq w c, grad := fun w => smul 2.0 (vsub w c) }

-- one step from 0 with η = 0.1: w = 0 - 0.1·2(0 - c) = 0.2·c
#test (gdStep quad 0.1 vzero).toList == [0.2, -0.4, 0.6000000000000001]
-- zero iterations return the start point
#test (gradientDescent quad ⟨0.1, 0⟩ c).toList == c.toList
-- converges to the minimiser
#test let w := gradientDescent quad ⟨0.1, 200⟩ vzero
  (List.finRange 3).all fun i => close w[i] c[i]
#test quad.loss (gradientDescent quad ⟨0.1, 200⟩ vzero) < 1e-12
-- many iterations stay fast (vectors are data, so there's no closure blow-up)
#test close (gradientDescent quad ⟨0.1, 20000⟩ vzero)[2] 3.0
-- the Hessian is 2I (L = 2): steps below 2/L = 1 converge, larger ones diverge
#test quad.loss (gradientDescent quad ⟨0.9, 1000⟩ vzero) < 1e-12
#test quad.loss (gradientDescent quad ⟨1.1, 100⟩ vzero) > 1.0
