module

public import LeanSMILES.API.Loader
public import LeanSMILES.MachineLearning.Definitions

/-!
# Featurization

Turns validated records into an ML `Dataset` with feature vectors:

* `fingerprintFeatures`: Morgan fingerprint bits as `0/1` features (the notebook's
  `GetMorganGenerator(radius, fpSize)`);
* `descriptorFeatures`: the six precomputed Delaney descriptors;
* `concatFeatures`: both at once;
* `StandardScaler`: per-feature standardization `(x - μ) / σ`, fitted on the training set
  only, like `sklearn.preprocessing.StandardScaler`.
-/

@[expose] public section

namespace API

open Primitives ML

variable {α : Type} [Scalar α]

/-- A way to turn a validated record into `n` features. -/
abbrev Featurizer (α : Type) (n : Nat) := ValidRecord → Vec α n

/-- Morgan fingerprint features of a molecule (usable on new SMILES, not just records). -/
def moleculeFingerprint (radius nBits : Nat) (m : Chem.Molecule) : Vec α nBits :=
  (m.morganFingerprint radius nBits).toFeatures

def fingerprintFeatures (radius nBits : Nat) : Featurizer α nBits :=
  fun r => moleculeFingerprint radius nBits r.molecule

def descriptorFeatures : Featurizer α 6 := fun r => r.descriptors.map Decimal.toScalar

def concatFeatures {a b : Nat} (f : Featurizer α a) (g : Featurizer α b) : Featurizer α (a + b) :=
  fun r => f r ++ g r

/-- Measured log-solubility of every record. -/
def targets (records : Array ValidRecord) : Vec α records.size :=
  Vector.ofFn fun i => records[i].logS.toScalar

/-- The feature matrix and target vector, one row per record (in order). -/
def toDataset {n : Nat} (records : Array ValidRecord) (featurize : Featurizer α n) :
    Dataset α records.size n :=
  { X := Vector.ofFn fun i => featurize records[i], y := targets records }

/-! ## Standardization -/

/-- Per-feature mean and standard deviation. -/
structure StandardScaler (α : Type) (n : Nat) where
  mean : Vec α n
  scale : Vec α n

namespace StandardScaler

variable {m n : Nat}

/-- Fit on the rows of `X`: population standard deviation (sklearn's `ddof = 0`). A
constant feature gets scale `1`, so it maps to `0` instead of dividing by zero. -/
def fit (X : Mat α m n) : StandardScaler α n :=
  let μ := colMean X
  let var := Vector.ofFn fun (j : Fin n) =>
    (sumFin fun (i : Fin m) => (X[i][j] - μ[j]) * (X[i][j] - μ[j])) / Scalar.fromNat m
  { mean := μ, scale := var.map fun v => if v ≤ 0 then 1 else Scalar.sqrt v }

def transformVec (sc : StandardScaler α n) (x : Vec α n) : Vec α n :=
  Vector.ofFn fun j => (x[j] - sc.mean[j]) / sc.scale[j]

def transform (sc : StandardScaler α n) (X : Mat α m n) : Mat α m n := X.map sc.transformVec

def transformDataset (sc : StandardScaler α n) (d : Dataset α m n) : Dataset α m n :=
  { d with X := sc.transform d.X }

end StandardScaler

end API

end
