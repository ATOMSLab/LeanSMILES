import LeanSMILES.MachineLearning.Executables
import LeanSMILES.MetaPrograms.Test

/-! Tests that the `Float` executables (`ML.Exec`) agree with the generic definitions
at `α := Float`, and tests for the loss-history variants. -/

open Primitives

def X : ML.Exec.Mat 5 2 :=
  #v[#v[0.0, 0.0], #v[1.0, 0.0], #v[0.0, 1.0], #v[2.0, 3.0], #v[-1.0, 4.0]]
def data : ML.Exec.Dataset 5 2 :=
  { X := X, y := Vector.ofFn fun i => 2.0 * X[i][0] - 3.0 * X[i][1] + 1.0 }

#test (ML.Exec.olsFit data).weights.toList == (ML.olsFit data).weights.toList
#test (ML.Exec.linRegGD ⟨0.02, 500⟩ data).bias == (ML.linRegGD ⟨0.02, 500⟩ data).bias
#test ML.Exec.dot #v[1.0, 2.0] #v[3.0, 4.0] == dot #v[1.0, 2.0] #v[3.0, 4.0]
#test (ML.Exec.perceptronFit ⟨1.0, 5⟩ data).bias == (ML.perceptronFit ⟨1.0, 5⟩ data).bias

-- the history variant returns the same model as `linRegGD`
def withHistory := ML.Exec.linRegGDWithHistory ⟨0.02, 500⟩ data 50
#eval withHistory.2
#test withHistory.1.bias == (ML.Exec.linRegGD ⟨0.02, 500⟩ data).bias
#test withHistory.2.map (·.1) == #[0, 50, 100, 150, 200, 250, 300, 350, 400, 450, 500]
-- the training loss never increases
#test (withHistory.2.toList.zip withHistory.2.toList.tail).all fun (a, b) => b.2 ≤ a.2
