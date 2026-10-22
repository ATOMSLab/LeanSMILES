module

public import LeanSMILES.Data.CSVparser
-- The same modules again as `meta` imports: the `#eval`s run their code at elaboration time.
meta import LeanSMILES.Data.CSVparser

open CSVparser

public section

def records := load "datasets/delaney-processed.csv"
#eval records
#eval records[1].smiles
#eval records[1].get .measuredLogSolubility

def recordsSmilesOnly := load "datasets/delaney-processed.csv" []
#eval recordsSmilesOnly
#eval recordsSmilesOnly[0]
