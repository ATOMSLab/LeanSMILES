module

public import LeanLearn.Classification.Logistic
public import LeanLearn.Classification.ROC
public import Pipelines.Representation

/-!
# Logistic regression test: EGFR classification vs scikit-learn

Reads `datasets/egfr-classification.csv` (from `tools/sklearn_egfr.py`): the
EGFR actives/inactives of ENCH 470 Lecture 21 with scikit-learn's train/test
split, plus the 5 FDA drugs, each with RDKit's Morgan on-bits and scikit-learn's
`LogisticRegression` probability and class. Two checks, run from the
repository root:

    lake exe logistic-test

1. **Solver.** Train `fitLogistic` on RDKit's bits, the exact features
   scikit-learn saw: every probability must agree to 10⁻⁶.
2. **Pipeline.** Train on Lean's own features (`morganFeatures`: parse,
   `Molecule.aromatize`, `Fingerprint/Morgan.lean`). They must equal RDKit's
   bits on every molecule, and every probability must agree to 10⁻⁶.

Each stage also reports test-set precision, recall and F1 (active = positive) and the
ROC AUC (`rocAuc`), next to the AUC of scikit-learn's probabilities.
-/

open LeanLearn.Classification Pipelines

structure Row where
  name : String
  smiles : String
  label : Option Bool
  split : String
  skProba : Float
  skPred : Bool
  rdkitBits : SparseBits
  deriving Inhabited

/-- A non-negative decimal like `0.659784941795`. -/
def parseFloat (s : String) : Float :=
  match s.splitOn "." with
  | [i, f] => Float.ofScientific (i ++ f).toNat! true f.length
  | _ => s.toNat!.toFloat

/-- Train on the labelled rows of `train`, then compare every row with scikit-learn.
Returns the largest probability difference, the rows whose class differs, and the model. -/
def compare (rows : Array Row) (feats : Array SparseBits) :
    IO (Float × List String × LogisticModel Float) := do
  let labelled (sp : String) := ((List.range rows.size).filterMap fun i =>
    match rows[i]!.split == sp, rows[i]!.label with
    | true, some y => some (feats[i]!, y) | _, _ => none).toArray
  let train := labelled "train"
  let test := labelled "test"
  let (model, iters) := fitLogistic (K := Float) {} 2048 train
  IO.println s!"  trained on {train.size} molecules in {iters} iterations; \
    train accuracy {accuracy model train}, test accuracy {accuracy model test}, \
    test confusion matrix {confusionMatrix model test}"
  let testIdx := (List.range rows.size).filter fun i ↦ rows[i]!.split == "test"
  let leanAuc := rocAuc (testIdx.toArray.filterMap fun i ↦
    rows[i]!.label.map fun y ↦ (model.proba feats[i]!, y))
  let skAuc := rocAuc (testIdx.toArray.filterMap fun i ↦ rows[i]!.label.map (rows[i]!.skProba, ·))
  let (tn, fp, fn, tp) := match confusionMatrix model test with
    | [[a, b], [c, d]] => (a, b, c, d) | _ => (0, 0, 0, 0)
  let precision := tp.toFloat / (tp + fp).toFloat
  let recall := tp.toFloat / (tp + fn).toFloat
  IO.println s!"  test precision {precision}, recall {recall}, \
    F1 {2 * precision * recall / (precision + recall)} (TN {tn}, FP {fp}, FN {fn}, TP {tp})"
  IO.println s!"  test ROC AUC {leanAuc} (from scikit-learn's probabilities: {skAuc})"
  let mut maxDiff : Float := 0
  let mut predMismatch : List String := []
  for i in [0:rows.size] do
    let r := rows[i]!
    maxDiff := max maxDiff (model.proba feats[i]! - r.skProba).abs
    if model.predict feats[i]! != r.skPred then predMismatch := predMismatch ++ [r.name]
  IO.println s!"  max |P_lean − P_sklearn| over {rows.size} molecules: {maxDiff}"
  IO.println s!"  predicted classes differing from scikit-learn: \
    {predMismatch.length} {predMismatch}"
  IO.println "  FDA drugs, P(active):"
  for i in [0:rows.size] do
    let r := rows[i]!
    if r.split == "fda" then
      IO.println s!"    {r.name}: lean {model.proba feats[i]!}  sklearn {r.skProba}"
  return (maxDiff, predMismatch, model)

public def main : IO UInt32 := do
  let lines := (← IO.FS.lines "datasets/egfr-classification.csv").toList.drop 1
  let rows := (lines.filterMap fun l => match l.splitOn "," with
    | [n, s, y, sp, p, pr, bits] =>
      let label := if y == "1" then some true else if y == "0" then some false else none
      let rdkit := ((bits.splitOn " ").filter (· ≠ "")).map String.toNat! |>.toArray
      some (Row.mk n s label sp (parseFloat p) (pr == "1") rdkit)
    | _ => none).toArray
  IO.println "1. solver, on RDKit's features [must match scikit-learn to 1e-6]"
  let (solverDiff, solverMismatch, _) ← compare rows (rows.map (·.rdkitBits))
  -- Morgan features in Lean (radius 2, 2048 bits)
  let mut feats : Array SparseBits := #[]
  for r in rows do
    match morganFeatures r.smiles with
    | .ok x => feats := feats.push x
    | .error e => do IO.println s!"cannot featurize {r.name}: {e}"; return 1
  let same := (List.range rows.size).countP fun i => feats[i]!.qsort (· < ·) == rows[i]!.rdkitBits
  IO.println s!"2. pipeline, on Lean's features [must match scikit-learn to 1e-6]"
  IO.println s!"  Lean's Morgan bits = RDKit's: {same}/{rows.size}"
  let (pipelineDiff, pipelineMismatch, _) ← compare rows feats
  return if solverMismatch.isEmpty && solverDiff < 0.000001 && same == rows.size
      && pipelineMismatch.isEmpty && pipelineDiff < 0.000001 then 0 else 1
