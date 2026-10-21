import LeanSMILES.API.Pipeline
import LeanSMILES.API.Split
import LeanSMILES.MachineLearning.Executables
import LeanSMILES.MetaPrograms.Cache
import LeanSMILES.MetaPrograms.Test

/-!
# SMILES → log solubility

Train a solubility model on the Delaney (ESOL) dataset and use it to predict the log
solubility (log₁₀ mol/L) of new SMILES strings with `predictSolubilityMessage`:

1. load `Data/delaney-processed.csv`, validate every SMILES, drop duplicate molecules;
2. featurize with radius-2, 4096-bit Morgan fingerprints and split 80/20 (seed 42);
3. fit least squares by gradient descent on the sparse fingerprint matrix
   (`ML.linRegGDSparse`, proved to give the same iterates as `ML.linRegGD`);
4. predict: SMILES → validated molecule → fingerprint → model score.

Run it with `lake lean LeanSMILES/Examples/PredictSolubility.lean` (about 2 seconds; plain
`lake env lean` does not load the precompiled native code and is much slower).
-/

open Primitives API

/-! ## Data -/

cached def cleaned : Array ValidRecord × CleaningReport :=
  clean ((CSV.parse (include_str "../Data/delaney-processed.csv") >>= (parseRecords ·)).toOption.getD #[])

#test cleaned.2.invalid.isEmpty && cleaned.1.size == 1115

abbrev nBits := 4096

cached def dataset : SizedSplit Float nBits :=
  trainTestSplitSized {} (toDataset cleaned.1 (fingerprintFeatures 2 nBits))

/-! ## Model

With 892 training molecules and 4096 bits there are more features than samples, so the
iteration count acts as regularization: 300 steps of size 0.1 give the best test score. -/

cached def model : ML.Exec.LinearModel nBits :=
  ML.Exec.linRegGDSparse { stepSize := 0.1, iters := 300 } dataset.train

#eval (evaluate model dataset.test).format
#test (evaluate model dataset.test).r2 > 0.7

def solubilityModel : FingerprintModel Float nBits := { radius := 2, model }

/-! ## Predictions

Edit the strings to try other molecules. An invalid SMILES gets the parser's error. -/

#eval predictSolubilityMessage solubilityModel "CCO"
#eval predictSolubilityMessage solubilityModel "c1ccc2ccccc2c1"
#eval predictSolubilityMessage solubilityModel "C1CC"
