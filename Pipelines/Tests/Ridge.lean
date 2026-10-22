/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanLearn.Regression.SparseRidge
public import LeanLearn.Regression.Metrics
public import LeanLearn.Plot.Parity
public import Pipelines.Representation

/-!
# Ridge regression test: Delaney log solubility vs scikit-learn

Reads `datasets/delaney-ridge.csv` (from `tools/sklearn_delaney.py`): the 1,128
Delaney molecules with measured log solubility, scikit-learn's
`train_test_split(test_size=0.20, random_state=0)`, RDKit's Morgan bits and
scikit-learn's `Ridge(alpha=1.0)` predictions. Two checks:

1. **Solver.** Train `fitRidge` on RDKit's bits, the exact features
   scikit-learn saw: every prediction must agree to 10⁻⁶.
2. **Pipeline.** Train on Lean's own features (`morganFeatures`: parse,
   `Molecule.aromatize`, Morgan). SMILES the parser rejects (OpenSMILES
   grammar deviations such as a ring label after a branch) are left out and
   listed. R², RMSE, MAE and the largest difference from scikit-learn are
   reported; the predictions differ slightly because the model is trained
   without the rejected molecules.

R², RMSE and MAE are computed in Lean for both. With `--svg PATH`, the pipeline
model's parity plot is written to `PATH`:

    lake exe ridge-test
    lake exe ridge-test --svg docs/figures/delaney-ridge-parity.svg
-/

open LeanLearn LeanLearn.Regression LeanLearn.Plot Pipelines

structure SolRow where
  name : String
  smiles : String
  logS : Float
  split : String
  skPred : Float
  rdkitBits : Array ℕ
  deriving Inhabited

/-- A decimal like `-3.077860875863` or `0.5`. -/
def parseSigned (s : String) : Float :=
  let neg := s.startsWith "-"
  let body := if neg then (s.drop 1).toString else s
  let v := match body.splitOn "." with
    | [i, f] => Float.ofScientific (i ++ f).toNat! true f.length
    | _ => body.toNat!.toFloat
  if neg then -v else v

/-- Fit on `feats`, report fit quality on both splits; returns the model's
predictions for every row. -/
def fitAndReport (rows : Array SolRow) (feats : Array (Array ℕ)) : IO (Array Float) := do
  let train := ((List.range rows.size).filterMap fun i ↦
    if rows[i]!.split == "train" then some (feats[i]!, rows[i]!.logS) else none).toArray
  let (model, iters) := SparseRidge.fit (K := Float) {} 2048 train
  let preds := feats.map model.predict
  let pairs (sp : String) := ((List.range rows.size).filterMap fun i ↦
    if rows[i]!.split == sp then some (rows[i]!.logS, preds[i]!) else none).toArray
  let skPairs (sp : String) := ((rows.toList.filter (·.split == sp)).map fun r ↦
    (r.logS, r.skPred)).toArray
  IO.println s!"  {train.size} training molecules, {iters} conjugate-gradient steps"
  for sp in ["train", "test"] do
    let (l, k) := (pairs sp, skPairs sp)
    IO.println s!"  {sp}: R² {fixed (r2 l) 4}, RMSE {fixed (rmse l) 4}, MAE {fixed (mae l) 4}   \
      (scikit-learn: R² {fixed (r2 k) 4}, RMSE {fixed (rmse k) 4}, MAE {fixed (mae k) 4})"
  return preds

public def main (args : List String) : IO UInt32 := do
  let lines := (← IO.FS.lines "datasets/delaney-ridge.csv").toList.drop 1
  let rows := (lines.filterMap fun l ↦ match l.splitOn "," with
    | [n, s, y, sp, p, bits] =>
      some { name := n, smiles := s, logS := parseSigned y, split := sp, skPred := parseSigned p,
             rdkitBits := (((bits.splitOn " ").filter (· ≠ "")).map String.toNat!).toArray }
    | _ => none).toArray
  let maxDiff (rs : Array SolRow) (preds : Array Float) : Float :=
    (List.range rs.size).foldl (fun m i ↦ max m (preds[i]! - rs[i]!.skPred).abs) 0
  IO.println "1. solver, on RDKit's features [must match scikit-learn to 1e-6]"
  let solverPreds ← fitAndReport rows (rows.map (·.rdkitBits))
  let solverDiff := maxDiff rows solverPreds
  IO.println s!"  max |prediction − scikit-learn| over {rows.size} molecules: {solverDiff}"
  -- Lean's own features; SMILES the parser rejects are left out of this stage
  let mut kept : Array SolRow := #[]
  let mut feats : Array (Array ℕ) := #[]
  let mut skipped : Array String := #[]
  for r in rows do
    match morganFeatures r.smiles with
    | .ok x => kept := kept.push r; feats := feats.push x
    | .error e => skipped := skipped.push s!"{r.name} ({r.split}): {e}"
  let same := (List.range kept.size).countP fun i ↦ feats[i]!.qsort (· < ·) == kept[i]!.rdkitBits
  IO.println "2. pipeline, on Lean's features [info]"
  IO.println s!"  {kept.size}/{rows.size} parsed; skipped {skipped.size} the parser rejects:"
  for s in skipped do
    IO.println s!"    {s}"
  IO.println s!"  Lean's Morgan bits = RDKit's: {same}/{kept.size}"
  let preds ← fitAndReport kept feats
  IO.println s!"  max |prediction − scikit-learn| over {kept.size} molecules: {maxDiff kept preds}"
  -- parity plot of the Lean pipeline
  if let ["--svg", path] := args then
    let series (sp label : String) (filled : Bool) : Series :=
      let pts := ((List.range kept.size).filterMap fun i ↦
        if kept[i]!.split == sp then some (kept[i]!.logS, preds[i]!) else none).toArray
      { label, points := pts, r2 := r2 pts, rmse := rmse pts, mae := mae pts, filled }
    IO.FS.writeFile path <| paritySvg "Delaney solubility: ridge on Morgan fingerprints"
      "LeanSMILES: parse, aromatize, Morgan (r = 2, 2048 bits), ridge α = 1; computed in Lean"
      "log solubility (log mol/L)"
      [series "train" "Training" false, series "test" "Test" true]
    IO.println s!"wrote {path}"
  return if solverDiff < 0.000001 then 0 else 1
