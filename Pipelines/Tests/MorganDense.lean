/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import Pipelines.Pipeline
public import Pipelines.Representation
public import LeanLearn.Regression.Metrics
public import LeanLearn.Plot.Parity

/-!
# Experiment: the verified dense solvers on folded Morgan bits

Runs the `Pipeline` solvers (`gaussSeidel`, `gradientDescent`: written once over the scalar,
with convergence theorems at `ℝ`) on `Representation.morgan 2 fpSize`, for several fold
sizes, on the website's Delaney slice. Reports wall time of `Pipeline.model Float` and
train/test R², so the fold size and solver for the demo can be chosen on numbers.

    lake exe morgan-dense-test [rows] [fpSize ...]
-/

open LeanSMILES LeanSMILES.SMILES LeanSMILES.Molecule
open LeanLearn LeanLearn.Regression LeanLearn.Plot Pipelines

/-- A decimal like `-0.77` as a rational. -/
def parseRatStr (s : String) : ℚ :=
  let s := s.trimAscii.toString
  let neg := s.startsWith "-"
  let body := if neg then (s.drop 1).toString else s
  let v : ℚ := match body.splitOn "." with
    | [i, f] => mkRat (i ++ f).toNat! (10 ^ f.length)
    | _ => (body.toNat! : ℚ)
  if neg then -v else v

structure Row where
  mol : Mol
  y : ℚ
  isTest : Bool

instance : Inhabited Row := ⟨{ mol := Mol.empty, y := 0, isTest := false }⟩

def runOne (train test : Array Row) (fp : ℕ) (ridge : ℚ) (name : String)
    (alg : Algorithm) : IO Unit := do
  let m := train.size
  let mQ : ℚ := m
  let yBar : ℚ := (train.foldl (fun acc r => acc + r.y) 0) / mQ
  let rep : Representation fp := Representation.morgan 2 fp
  let labelled : LabelledMolecules m :=
    { molecules := Vector.ofFn fun i => train[i.val]!.mol
      targets := Vector.ofFn fun i => train[i.val]!.y - yBar }
  let pipe : Pipeline m fp :=
    { data := labelled, representation := rep, ridge := ridge, algorithm := alg }
  let t0 ← IO.monoMsNow
  let θ : Vec Float (fp + 1) := pipe.model Float
  -- force the fit before reading the clock
  let checksum := θ.toList.foldl (· + ·) 0
  if checksum.isNaN then IO.println "  (nan)"
  let t1 ← IO.monoMsNow
  let yBarF := yBar.toFloat
  let pairs (rs : Array Row) : Array (Float × Float) :=
    rs.map fun r => (r.y.toFloat, pipe.predictWith θ r.mol + yBarF)
  let (tr, te) := (pairs train, pairs test)
  IO.println s!"  fp={fp} λ={ridge.toFloat} {name}: {t1 - t0} ms · train R² {fixed (r2 tr) 3} · \
    test R² {fixed (r2 te) 3} RMSE {fixed (rmse te) 3}"

public def main (args : List String) : IO UInt32 := do
  let limit := (args.head? >>= String.toNat?).getD 204
  let fps := (args.drop 1).filterMap String.toNat?
  let fps := if fps.isEmpty then [128, 256, 512] else fps
  let raw ← IO.FS.lines "datasets/delaney-processed.csv"
  let lines := (raw.toList.drop 1).take limit |>.toArray
  let mut rows : Array Row := #[]
  let mut skipped := 0
  for i in [0:lines.size] do
    let fields := lines[i]!.splitOn ","
    if fields.length < 3 then continue
    let smiles := fields.getLast!.trimAscii.toString
    let y := parseRatStr fields[fields.length - 2]!
    match parseAromatized smiles with
    | Except.ok M => rows := rows.push { mol := M, y := y, isTest := i % 5 == 0 }
    | Except.error _ => skipped := skipped + 1
  let train := rows.filter (!·.isTest)
  let test := rows.filter (·.isTest)
  IO.println s!"{rows.size} molecules ({skipped} skipped): {train.size} train, {test.size} test"
  -- the largest number of on-bits in a training molecule bounds ‖x‖², hence the smoothness
  let m := train.size
  for fp in fps do
    let rep : Representation fp := Representation.morgan 2 fp
    -- the smoothness Λ = (1/m) Σᵣ ‖xᵣ‖² + λ of `loss_gradientDescent_le_add`, exactly;
    -- the bias column adds 1 to every ‖xᵣ‖²
    let meanSq : ℚ :=
      (train.foldl (fun acc r => acc + (rep r.mol).toList.foldl (· + ·) 0) 0) / m + 1
    IO.println s!"fp={fp}: mean ‖x‖² {meanSq.toFloat}"
    for ridge in [mkRat 1 m, mkRat 1 20] do
      let η : ℚ := 1 / (2 * (meanSq + ridge))
      runOne train test fp ridge "GS 30" (.gaussSeidel 30)
      runOne train test fp ridge "GD 400" (.gradientDescent η 400)
      runOne train test fp ridge "GD 800" (.gradientDescent η 800)
  return 0
