/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
import Pipelines.Pipeline
import LeanSMILES.Data.CSVparser

/-!
# Pipelines.Data

Labelled molecules from the CSV tables in `datasets/`, read with the toolkit's
`CSVparser`. The parser reads numbers as `Float`; `ratOfFloat` recovers the exact decimal
they were written as (the Delaney table writes at most four decimals), so a pipeline's
targets stay exact rationals.
-/

namespace Pipelines

open LeanSMILES

/-- The rational `x` was written as, assuming it had at most `digits` decimals: `x`
rounded to `digits` decimal places. `ratOfFloat (-0.77) = -77/100`. -/
def ratOfFloat (x : Float) (digits : ℕ := 6) : ℚ :=
  mkRat (x * (10 : Float) ^ digits.toFloat).round.toInt64.toInt (10 ^ digits)

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
