/-
Copyright (c) 2026 Kevin Ishimwe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Ishimwe, Samiha Sharlin, Tyler Josephson
-/
module

public import LeanSMILES.Data.CSVparser
-- The same modules again as `meta` imports: the `#eval`s run their code at elaboration time.
meta import LeanSMILES.Data.CSVparser

/-!
# Example: reading the Delaney table

`CSVparser.load` on `datasets/delaney-processed.csv`, with and without the numeric columns.
-/

open CSVparser

public section

/-- The whole Delaney table: each row's SMILES and every feature in `Feature.all`. -/
def records := load "datasets/delaney-processed.csv"
#eval records
#eval records[1].smiles
#eval records[1].get .measuredLogSolubility

/-- The table read with no features: rows hold only `smiles`, so every `get` returns `0.0`. -/
def recordsSmilesOnly := load "datasets/delaney-processed.csv" []
#eval recordsSmilesOnly
#eval recordsSmilesOnly[0]
