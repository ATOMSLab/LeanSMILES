import LeanSMILES.Data.CSVparser
open CSVparser

def records := load "datasets/delaney-processed.csv"
#eval records
#eval records[1].smiles
#eval records[1].get .measuredLogSolubility



def recordsSmilesOnly := load "datasets/delaney-processed.csv" []
#eval recordsSmilesOnly
#eval recordsSmilesOnly[0]
