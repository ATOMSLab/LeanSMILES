import LeanSMILES.ML.Logistic

/-!
# Logistic regression test: EGFR classification vs scikit-learn

Reads `datasets/egfr-classification.csv` (from `tools/sklearn_egfr.py`): the
EGFR actives/inactives of ENCH 470 Lecture 21 with scikit-learn's train/test
split, plus the 5 FDA drugs. Computes Morgan features in Lean, trains
`fitLogistic` on the training rows, and compares with scikit-learn's
`LogisticRegression` on every molecule: predicted class, probability, test
accuracy and confusion matrix. Run from the repository root:

    lake exe logistic-test
-/

open LeanSMILES.ML

structure Row where
  name : String
  smiles : String
  label : Option Bool
  split : String
  skProba : Float
  skPred : Bool
  deriving Inhabited

/-- A non-negative decimal like `0.659784941795`. -/
def parseFloat (s : String) : Float :=
  match s.splitOn "." with
  | [i, f] => Float.ofScientific (i ++ f).toNat! true f.length
  | _ => s.toNat!.toFloat

def main : IO UInt32 := do
  let lines := (← IO.FS.lines "datasets/egfr-classification.csv").toList.drop 1
  let rows := lines.filterMap fun l => match l.splitOn "," with
    | [n, s, y, sp, p, pr] =>
      let label := if y == "1" then some true else if y == "0" then some false else none
      some (Row.mk n s label sp (parseFloat p) (pr == "1"))
    | _ => none
  -- Morgan features in Lean (radius 2, 2048 bits)
  let mut feats : Array SparseBits := #[]
  for r in rows do
    match Chem.morganFeatures r.smiles with
    | .ok x => feats := feats.push x
    | .error e => do IO.println s!"cannot featurize {r.name}: {e}"; return 1
  let labelled (sp : String) := (List.range rows.length).filterMap fun i =>
    match rows[i]!.split == sp, rows[i]!.label with
    | true, some y => some (feats[i]!, y) | _, _ => none
  let train := (labelled "train").toArray
  let test := (labelled "test").toArray
  let (model, iters) := fitLogistic (K := Float) {} 2048 train
  IO.println s!"trained on {train.size} molecules in {iters} iterations"
  IO.println s!"train accuracy {accuracy model train}, test accuracy {accuracy model test}"
  IO.println s!"test confusion matrix {confusionMatrix model test}"
  -- compare every molecule with scikit-learn
  let mut maxDiff : Float := 0
  let mut predMismatch : List String := []
  for i in [0:rows.length] do
    let r := rows[i]!
    let p := model.proba feats[i]!
    maxDiff := max maxDiff (p - r.skProba).abs
    if model.predict feats[i]! != r.skPred then predMismatch := predMismatch ++ [r.name]
  IO.println s!"max |P_lean − P_sklearn| over {rows.length} molecules: \
    {maxDiff * 1000000000} × 10⁻⁹"
  IO.println s!"predicted classes differing from scikit-learn: {predMismatch.length} {predMismatch}"
  IO.println "FDA drugs (P(active)):"
  for i in [0:rows.length] do
    let r := rows[i]!
    if r.split == "fda" then
      IO.println s!"  {r.name}: lean {model.proba feats[i]!}  sklearn {r.skProba}"
  return if predMismatch.isEmpty && maxDiff < 0.000001 then 0 else 1
