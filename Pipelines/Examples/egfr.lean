import LeanLearn.Classification.Logistic
import Pipelines.Representation
open LeanLearn.Classification Pipelines

/-!
# Example: EGFR classification with Morgan fingerprints (ENCH 470 Lecture 21)

Can we tell EGFR inhibitors (actives) from inactive molecules by their Morgan
fingerprints? Lecture 21 does this in Python with RDKit + scikit-learn; here
every step runs in Lean:

| Lecture 21 (Python) | Lean |
|---|---|
| `rdFingerprintGenerator.GetFPs(mols)` | `morganFeatures s` (2048 bits) |
| `y = 1` active, `0` inactive | `true` / `false` |
| `train_test_split(test_size=0.20, random_state=0)` | the same split, read from the data file |
| `LogisticRegression(random_state=0).fit(X, y)` | `fitLogistic {} 2048 train` |
| `clf.score`, `confusion_matrix` | `accuracy`, `confusionMatrix` |
| `clf.predict_proba(fda_fps)` | `model.proba` |

`lake exe logistic-test` checks these results against scikit-learn molecule by
molecule. Click on an `#eval` line to see its result in the Infoview. The big
`#eval` trains the model (about half a minute in the editor; the compiled test
takes about a second).
-/

-- A molecule becomes the list of its on-bits (about 40 of 2048 for drug-like molecules)
#eval morganFeatures "CCO"                    -- ethanol: 6 bits

-- The logistic function turns a score into a probability
#eval [-4.0, -1.0, 0.0, 1.0, 4.0].map (sigmoid (K := Float))

/-- One row of `datasets/egfr-classification.csv`: name, SMILES, label (active?), split. -/
structure Compound where
  name : String
  smiles : String
  active : Option Bool
  split : String

/-- The 200 ChEMBL molecules (with scikit-learn's train/test split) and the 5 FDA drugs. -/
def loadMolecules : IO (Array Compound) := do
  let lines := (← IO.FS.lines "datasets/egfr-classification.csv").toList.drop 1
  return (lines.filterMap fun l => match l.splitOn "," with
    | [n, s, y, sp, _, _, _] =>
      some ⟨n, s, if y == "1" then some true else if y == "0" then some false else none, sp⟩
    | _ => none).toArray

/-- Features and labels of the molecules in one split. -/
def dataset (mols : Array Compound) (split : String) : Array (SparseBits × Bool) :=
  mols.filterMap fun m => match m.split == split, m.active, morganFeatures m.smiles with
    | true, some y, .ok x => some (x, y)
    | _, _, _ => none

-- Lecture 21, start to finish
#eval show IO Unit from do
  let mols ← loadMolecules
  let train := dataset mols "train"
  let test := dataset mols "test"
  IO.println s!"{train.size} training molecules, {test.size} test molecules"
  -- fit (a looser stopping tolerance than the test; the predictions are the same)
  let (model, iters) := fitLogistic (K := Float) { tol := 0.000001 } 2048 train
  IO.println s!"trained in {iters} iterations"
  IO.println s!"train accuracy {accuracy model train}"
  IO.println s!"test accuracy  {accuracy model test}"
  IO.println s!"confusion matrix (rows: true inactive/active, columns: predicted) \
    {confusionMatrix model test}"
  -- the five FDA-approved EGFR drugs
  IO.println "FDA drugs, P(active):"
  for m in mols.filter (·.split == "fda") do
    if let .ok x := morganFeatures m.smiles then
      IO.println s!"  {m.name}: {model.proba x}"
  -- the fingerprint bits with the largest weights (positive = points to "active")
  let top := ((List.range 2048).map fun j => (j, model.weights[j]!)).mergeSort
    (fun a b => a.2.abs ≥ b.2.abs) |>.take 5
  IO.println s!"largest weights (bit, weight): {top}"
  -- any new SMILES
  for s in ["c1ccccc1", "COc1cc2ncnc(Nc3ccccc3)c2cc1OC"] do
    if let .ok x := morganFeatures s then
      IO.println s!"  {s}: P(active) = {model.proba x}"
