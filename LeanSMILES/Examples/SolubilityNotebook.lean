import LeanSMILES.API.Pipeline
import LeanSMILES.API.Split
import LeanSMILES.Machine_Learning.EXECUTABLES
import LeanSMILES.MetaPrograms.Cache
import LeanSMILES.MetaPrograms.Show
import LeanSMILES.MetaPrograms.Test

/-!
# Machine Learning for Aqueous Solubility (ESOL)

The ENCH 640 final project notebook (`ENCH 640-final project.ipynb`), redone in Lean on
the project's Delaney (ESOL) dataset: predict measured log solubility (log₁₀ mol/L) from
SMILES instead of emission wavelength. Every Python cell has a counterpart below, and every
figure is a widget: open this file and put the cursor on a `#show` line to see it in the
infoview.

| notebook                                   | here                                        |
|--------------------------------------------|---------------------------------------------|
| `pd.read_csv`, `df.isnull().sum()`         | `CSV.parse`, `CSV.missingCounts`            |
| `Chem.MolFromSmiles` / `MolToSmiles`       | `clean` (validate, canonicalize, dedupe)    |
| `sns.histplot`                             | `Widgets.histogram`                         |
| `GetMorganGenerator(radius=2, fpSize=4096)` | `fingerprintFeatures 2 4096`               |
| `train_test_split(test_size=0.20, random_state=42)` | `trainTestSplitSized {}`           |
| `RandomForestRegressor`                    | `ML.Exec.linRegGDWithHistory` (see §6)      |
| `mean_squared_error`, `r2_score`           | `API.evaluate`                              |
| `plt.scatter` measured vs. predicted       | `Widgets.scatter`                           |
| `predict_wavelength_from_smiles`           | `predictSolubilityMessage`                  |

Run it with `lake lean LeanSMILES/Examples/SolubilityNotebook.lean` (a few seconds; plain
`lake env lean` does not load the precompiled native code and is much slower).
-/

open Primitives API Widgets MetaPrograms

/-! ## 2. Data Preparation

Load the CSV and check it for missing values, zero SMILES, and the range of the target. -/

cached def csv : CSV :=
  (CSV.parse (include_str "../Data/delaney-processed.csv")).toOption.getD default

-- `print('Missing values:', df.isnull().sum())`
#show keyValueTable (csv.missingCounts.map fun (c, k) => (c, s!"{k}")) "Missing values"

cached def records : Array SolubilityRecord := (parseRecords csv).toOption.getD #[]

def logSOf (rs : Array SolubilityRecord) : Array Float := rs.map (·.logS.toFloat)

-- `(df['smiles'] == 0).sum()`
#eval s!"Zero SMILES: {(records.filter (·.smiles.str == "0")).size}"

-- `df['measured ...'].mean()`, `.min()`, `.max()`
#show describe (Vector.mk (logSOf records) rfl)

-- The notebook fills missing emission values with `df.fillna(695)`. The solubility data
-- has none, so there is nothing to fill.
#test csv.missingCounts.all (·.2 == 0)

-- `df.head(10)`
#show csv

/-! ## 3. SMILES Cleaning Pipeline

1. Canonicalize every SMILES.
2. Remove invalid SMILES entries.
3. Eliminate duplicate molecules based on canonical SMILES (the first occurrence wins). -/

cached def cleaned : Array ValidRecord × CleaningReport := clean records

#show cleaned.2
#show cleaned.1

#test cleaned.2.invalid.isEmpty && cleaned.1.size == 1115

/-! ## 4. Log Solubility Distribution -/

#show histogram (cleaned.1.map (·.logS.toFloat)) 30 "Log Solubility Distribution"
  "Measured log solubility (log mol/L)" "Frequency" "purple"

/-! ## 5. Feature Extraction

Morgan fingerprints with radius 2 (atom neighbourhoods up to 2 bonds away) and 4096 bits,
as 0/1 features. The label is the measured log solubility. -/

abbrev nBits := 4096

cached def dataset : SizedSplit Float nBits :=
  trainTestSplitSized {} (toDataset cleaned.1 (fingerprintFeatures 2 nBits))

/-! ## 6. Machine Learning Model

The notebook trains `RandomForestRegressor(n_estimators=100)`. The library has no tree
models, so this uses its verified linear regression: least squares on the fingerprint
bits, fitted by gradient descent from zero (`ML.linRegGD`, whose convergence is stated in
`Machine_Learning/PROOFS.lean`). With 892 molecules and 4096 bits there are more features
than samples, so the iteration count acts as regularization: 300 steps of size 0.1 give
the best test score, and training longer only overfits.

The split is 80/20 with seed 42 (`random_state=42`); the rows drawn differ from sklearn's,
because the shuffle is SplitMix64, not NumPy. -/

#eval s!"train: {dataset.trainSize}, test: {dataset.testSize}"
#test dataset.trainSize == 892 && dataset.testSize == 223

def gdConfig : ML.Exec.GDConfig := { stepSize := 0.1, iters := 300 }

-- the trained model and its training MSE every 10 iterations
cached def trained : ML.Exec.LinearModel nBits × Array (Nat × Float) :=
  ML.Exec.linRegGDWithHistory gdConfig dataset.train 10

def model : ML.Exec.LinearModel nBits := trained.1

#show lineChart #[("training MSE", "crimson", trained.2.map fun (k, l) => (k.toFloat, l))]
  "Gradient descent" "Iteration" "Mean squared error"

/-! ## 7. Model Performance on Training Set -/

def measuredVsPredicted {m : Nat} (d : ML.Exec.Dataset m nBits) : Array (Float × Float) :=
  d.y.toArray.zip (model.predictAll d.X).toArray

#show evaluate model dataset.train

/-! ## 8. Visualization: Measured vs. Predicted Log Solubility (Training Set)

The dashed green line is perfect prediction. `Widgets.saveSVG` writes a figure to a file,
like `plt.savefig`. -/

#show scatter (measuredVsPredicted dataset.train) "Measured vs Predicted for Training Set"
  "Measured log solubility" "Predicted log solubility" "crimson" 0.3

/-! ## 9. Model Performance on Test Set

Performance on the 20% of molecules the model has not seen. -/

#show evaluate model dataset.test

#test (evaluate model dataset.test).r2 > 0.7

/-! ## 10. Visualization: Measured vs. Predicted Log Solubility (Test Set) -/

#show scatter (measuredVsPredicted dataset.test) "Measured vs Predicted for Test Set"
  "Measured log solubility" "Predicted log solubility" "purple" 0.4

#show row #[
  scatter (measuredVsPredicted dataset.train) "Training set" "Measured" "Predicted" "crimson" 0.3,
  scatter (measuredVsPredicted dataset.test) "Test set" "Measured" "Predicted" "purple" 0.4]

/-! ## 11. End-to-End ML Pipeline: SMILES to Log Solubility

Takes a SMILES string, validates it, converts it to a Morgan fingerprint, and predicts its
log solubility with the trained model. The notebook reads SMILES in an `input()` loop; here
each query is an `#eval` (edit the strings to try others). -/

def solubilityModel : FingerprintModel Float nBits := { radius := 2, model }

#eval predictSolubilityMessage solubilityModel "CCO"
#eval predictSolubilityMessage solubilityModel "c1ccc2ccccc2c1"
#eval predictSolubilityMessage solubilityModel "C1CC"

def queries : Array (String × String) := #[
  ("CCO", "ethanol"), ("c1ccccc1", "benzene"), ("c1ccc2ccccc2c1", "naphthalene"),
  ("CC(=O)Oc1ccccc1C(=O)O", "aspirin"), ("CN1C=NC2=C1C(=O)N(C(=O)N2C)C", "caffeine"),
  ("ClC(Cl)(Cl)Cl", "carbon tetrachloride"), ("OCC(O)CO", "glycerol"),
  ("CC(C)Cc1ccc(cc1)C(C)C(=O)O", "ibuprofen")]

def predictionCaption (s name : String) : String :=
  match solubilityModel.predict s with
  | .ok y => s!"{name}: logS ≈ {formatFloat y 2}"
  | .error _ => s!"{name}: invalid"

#show moleculeGrid (queries.map fun (s, name) => (s, predictionCaption s name)) 4 220
