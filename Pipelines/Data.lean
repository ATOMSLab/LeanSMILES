/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
-/
module

public import Pipelines.Pipeline
public import LeanSMILES.Data.CSVparser

/-!
# Pipelines.Data

Labelled molecules from the CSV tables in `datasets/`, read with the toolkit's
`CSVparser`. The parser reads numbers as `Float`; `ratOfFloat` recovers the exact decimal
they were written as (the Delaney table writes at most four decimals), so a pipeline's
targets stay exact rationals.
-/

@[expose] public section

namespace Pipelines

open LeanSMILES

/-- The rational `x` was written as, assuming it had at most `digits` decimals: `x`
rounded to `digits` decimal places. `ratOfFloat (-0.77) = -77/100`. -/
def ratOfFloat (x : Float) (digits : ℕ := 6) : ℚ :=
  mkRat (x * (10 : Float) ^ digits.toFloat).round.toInt64.toInt (10 ^ digits)

/-- The exact rational value of a finite `Float`: `|x| = f · 2ᵉ` with `f ∈ [1/2, 1)`
(`Float.frExp`), and `f · 2⁵³` is an integer for every normal double, so
`|x| = (f · 2⁵³) / 2^(53 - e)`. Non-finite values read as `0`. Reading a trained `Float` model
this way is what lets the exact residual certificate (`Pipeline.checkResidual`) cover the
numbers that are actually shown. -/
def ratOfFloatExact (x : Float) : ℚ :=
  if !x.isFinite || x == 0 then 0 else
    let (f, e) := x.abs.frExp
    let mant : ℤ := (f.scaleB 53).toUInt64.toNat
    let q : ℚ := if e ≥ 53 then mant * 2 ^ (e - 53).toNat else mkRat mant (2 ^ (53 - e).toNat)
    if x < 0 then -q else q

namespace LabelledMolecules

/-- `count` rows of a CSV table, starting at row `start`, labelled by one of its columns
(by default the measured log solubility). Every SMILES must parse. -/
def ofRecords (records : Array CSVparser.Molecule) (start count : ℕ)
    (target : CSVparser.Feature := .measuredLogSolubility) : LabelledMolecules count :=
  let rows : Vector CSVparser.Molecule count := Vector.ofFn fun i ↦ records[start + i.val]
  { molecules := rows.map fun r ↦ Mol.ofSmiles! r.smiles
    targets := rows.map fun r ↦ ratOfFloat (r.get target) }

end LabelledMolecules

end Pipelines
