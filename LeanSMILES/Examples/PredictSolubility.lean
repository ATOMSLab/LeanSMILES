import LeanSMILES.API.Pipeline
import LeanSMILES.API.Split
import LeanSMILES.MachineLearning.Executables
import LeanSMILES.MetaPrograms.Cache
import LeanSMILES.MetaPrograms.Test

/-!
# SMILES → log solubility

Train three linear models on the Delaney (ESOL) dataset, compare them on the same held-out
molecules, and use them to predict the solubility of new SMILES strings:

| model            | features                          | trained by                      | predicts        |
|------------------|-----------------------------------|---------------------------------|-----------------|
| gradient descent | radius-2, 4096-bit Morgan bits    | `linRegGDSparse` (least squares) | log solubility  |
| OLS              | 6 descriptors computed from SMILES | `olsFit` (normal equations)     | log solubility  |
| perceptron       | radius-2, 4096-bit Morgan bits    | `perceptronFit`                 | soluble or not  |

OLS runs on descriptors because on 4096 fingerprint bits the normal equations are
singular (more features than the 892 training molecules). The perceptron is a classifier,
so all three models are also compared on one classification task: is the molecule
soluble, `logS ≥ -2` (at least 10 mmol/L)?

Run it with `lake lean LeanSMILES/Examples/PredictSolubility.lean` (about 4 seconds; plain
`lake env lean` does not load the precompiled native code and is much slower).
-/

open Primitives API

/-! ## Data

Both feature sets come from the same cleaned records and the same split (seed 42), so
every model is trained and tested on the same molecules. -/

cached def cleaned : Array ValidRecord × CleaningReport :=
  clean ((CSV.parse (include_str "../Data/delaney-processed.csv") >>= (parseRecords ·)).toOption.getD #[])

#test cleaned.2.invalid.isEmpty && cleaned.1.size == 1115

abbrev nBits := 4096

cached def dataset : SizedSplit Float nBits :=
  trainTestSplitSized {} (toDataset cleaned.1 (fingerprintFeatures 2 nBits))

cached def descriptorData : SizedSplit Float 6 :=
  trainTestSplitSized {} (toDataset cleaned.1 computedDescriptorFeatures)

#test descriptorData.test.y.toList == dataset.test.y.toList

/-- The classification threshold: soluble means `logS ≥ -2`. -/
def threshold : Float := -2.0

/-! ## Model 1: least squares by gradient descent on fingerprints

With 892 training molecules and 4096 bits there are more features than samples, so the
iteration count acts as regularization (200 steps of size 0.1 here). -/

cached def model : ML.Exec.LinearModel nBits :=
  ML.Exec.linRegGDSparse { stepSize := 0.1, iters := 200 } dataset.train

#test (evaluate model dataset.test).r2 > 0.7

def solubilityModel : FingerprintModel Float nBits := { radius := 2, model }

/-! ## Model 2: ordinary least squares on descriptors

Solves the normal equations exactly for molecular weight, heavy atoms, H-bond donors,
rings, rotatable bonds and minimum degree. -/

cached def olsModel : ML.Exec.LinearModel 6 := ML.Exec.olsFit descriptorData.train

#eval olsModel.weights.toList.map (formatFloat · 4)

/-! ## Model 3: perceptron on fingerprints

Trained on `±1` labels (`+1` = soluble). 10 epochs gave the best test accuracy; the
classes are not linearly separable, so more epochs start to overfit. -/

cached def perceptron : ML.Exec.LinearModel nBits :=
  ML.Exec.perceptronFit { learningRate := 1.0, epochs := 10 } (binarize threshold dataset.train)

/-! ## Comparison on the 223 test molecules -/

def pad (s : String) (w : Nat) : String := s ++ String.ofList (List.replicate (w - s.length) ' ')

def row (cells : List String) : String :=
  String.join (cells.zipIdx.map fun (c, k) => pad c (if k == 0 then 34 else 10))

-- regression: RMSE and MAE in log(mol/L)
#eval IO.println <| "\n".intercalate (row ["model", "RMSE", "MAE", "R²"] ::
  [("gradient descent (fingerprints)", evaluate model dataset.test),
   ("OLS (descriptors)", evaluate olsModel descriptorData.test)].map fun (name, r) =>
    row [name, formatFloat r.rmse 3, formatFloat r.mae 3, formatFloat r.r2 3])

/-- Test accuracy of `±1` predictions against the true classes. -/
def testAccuracy {m : Nat} (y pred : Vec Float m) : Float := accuracy (labelsAt threshold y) pred

-- classification: soluble (logS ≥ -2) or not
#eval IO.println <| "\n".intercalate (row ["model", "accuracy"] ::
  [("always \"insoluble\"", testAccuracy dataset.test.y (Vector.replicate _ (-1))),
   ("gradient descent, thresholded", testAccuracy dataset.test.y
      (labelsAt threshold (model.predictAll dataset.test.X))),
   ("OLS, thresholded", testAccuracy descriptorData.test.y
      (labelsAt threshold (olsModel.predictAll descriptorData.test.X))),
   ("perceptron", testAccuracy dataset.test.y (labelsAt 0 (perceptron.predictAll dataset.test.X)))].map
    fun (name, a) => row [name, s!"{formatFloat (100 * a) 1} %"])

#test testAccuracy dataset.test.y (labelsAt 0 (perceptron.predictAll dataset.test.X)) > 0.8

/-! ## Predictions

Edit the strings to try other molecules. An invalid SMILES gets the parser's error. -/

#eval predictSolubilityMessage solubilityModel "CCO"
#eval predictSolubilityMessage solubilityModel "c1ccc2ccccc2c1"
#eval predictSolubilityMessage solubilityModel "C1CC"

/-- All three models on one SMILES string. -/
def compareModels (s : String) : String :=
  match parseValid s with
  | .error e => row [s, s!"invalid SMILES ({e})"]
  | .ok m =>
    let gd := model.score (moleculeFingerprint 2 nBits m)
    let ols := olsModel.score (moleculeDescriptors m)
    let soluble := 0 ≤ perceptron.score (moleculeFingerprint 2 nBits m)
    row [s, formatFloat gd 2, formatFloat ols 2, if soluble then "soluble" else "insoluble"]

#eval IO.println <| "\n".intercalate (row ["SMILES", "GD logS", "OLS logS", "perceptron"] ::
  ["CCO", "c1ccc2ccccc2c1", "CC(=O)Oc1ccccc1C(=O)O", "ClC(Cl)(Cl)Cl", "C1CC"].map compareModels)
