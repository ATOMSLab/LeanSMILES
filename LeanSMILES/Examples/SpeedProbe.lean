import LeanSMILES.API.Pipeline
import LeanSMILES.API.Split
import LeanSMILES.Machine_Learning.EXECUTABLES
import LeanSMILES.MetaPrograms.Cache
open Primitives API

cached def valid : Array ValidRecord :=
  (clean ((CSV.parse (include_str "../Data/delaney-processed.csv") >>= (parseRecords ·)).toOption.getD #[])).1
cached def split : SizedSplit Float 2048 :=
  trainTestSplitSized {} (toDataset valid (fingerprintFeatures 2 2048))
cached def model : ML.Exec.LinearModel 2048 := ML.Exec.linRegGD ⟨0.02, 300⟩ split.train
#eval model.bias
#eval model.bias + 1
#eval model.bias + 2
#eval model.bias + 3
#eval model.bias + 4
#eval model.bias + 5
#eval (API.evaluate model split.test).r2
