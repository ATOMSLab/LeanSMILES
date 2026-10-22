import LeanSMILES.Data.CSVparser
open CSVparser

def records := load "datasets/delaney-processed.csv"
#eval records
#eval records[1].smiles
#eval records[1].get .molecularWeight



def recordsonlymolWeight := load "datasets/delaney-processed.csv" []
#eval recordsonlymolWeight
#eval recordsonlymolWeight[0]
