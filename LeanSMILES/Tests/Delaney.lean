import LeanSMILES.API.Features
import LeanSMILES.MachineLearning.Executables
import LeanSMILES.MetaPrograms.Test
import LeanSMILES.MetaPrograms.Cache

/-! Tests on the real dataset `Data/delaney-processed.csv`: loading, validation and
cleaning, descriptors against the dataset's RDKit values, and least squares against an
exact reference. -/

open Primitives ML API

cached def csv : CSV := (CSV.parse (include_str "../Data/delaney-processed.csv")).toOption.getD default
cached def records : Array SolubilityRecord := (parseRecords csv).toOption.getD #[]
cached def cleaned : Array ValidRecord × CleaningReport := clean records

#eval (csv.rows.size, csv.header.size)
#eval repr cleaned.2

#test csv.rows.size == 1128 && csv.header.size == 10
#test csv.missingCounts.all (·.2 == 0)
#test records.size == 1128
#test records[0]!.compoundId == "Amigdalin" && records[0]!.logS == ⟨-77, -2⟩
-- every SMILES in the dataset is valid
#test cleaned.2.invalid.isEmpty
#test cleaned.2.duplicates.size == 13 && cleaned.1.size == 1115

/-! Descriptors computed from the SMILES agree with the dataset's RDKit columns. -/

def nat (d : Decimal) : Nat := d.toFloat.toUInt64.toNat
def agree (f : ValidRecord → Bool) : Nat := (cleaned.1.filter f).size

#eval agree fun r => r.molecule.ringCount == nat r.descriptors[3]

#test agree (fun r =>
  (r.molecule.molecularWeight (α := Float) - r.descriptors[1].toFloat).abs < 0.0005) == 1115
#test agree (fun r => r.molecule.hDonorCount == nat r.descriptors[2]) == 1115
#test agree (fun r => r.molecule.rotatableBondCount == nat r.descriptors[4]) == 1115
#test agree (fun r => r.molecule.minDegree == nat r.descriptors[0]) == 1115
-- RDKit's symmetrized SSSR counts one extra ring for 3 bridged bicyclics
#test agree (fun r => r.molecule.ringCount == nat r.descriptors[3]) == 1112

/-! Least squares on all 1128 rows and the 6 descriptors. The reference coefficients come
from solving the normal equations exactly with Python's `fractions.Fraction`. -/

cached def fitted : List Float :=
  let X : ML.Exec.Mat records.size 6 :=
    Vector.ofFn fun i => records[i].descriptors.map Decimal.toFloat
  let y : ML.Exec.Vec records.size := Vector.ofFn fun i => records[i].logS.toFloat
  let model := ML.Exec.olsFit { X, y }
  model.weights.toList ++ [model.bias]

def reference : List Float :=
  [-0.49921068, -0.01362162, 0.07281654, -0.41338402, -0.14337233, 0.03159255, -0.00934896]

#eval fitted
#test (fitted.zip reference).all fun (a, b) => (a - b).abs < 1e-7

/-! Sparse gradient descent on fingerprint features gives bit-for-bit the same model as
the dense solver (proved equal over `ℝ` as `ML.linRegGDSparse_eq`). -/

cached def fingerprints : ML.Exec.Dataset cleaned.1.size 1024 :=
  toDataset cleaned.1 (fingerprintFeatures 2 1024)

#test let cfg : ML.Exec.GDConfig := { stepSize := 0.1, iters := 20 }
  let s := ML.Exec.linRegGDSparse cfg fingerprints
  let d := ML.Exec.linRegGD cfg fingerprints
  s.weights == d.weights && s.bias == d.bias
