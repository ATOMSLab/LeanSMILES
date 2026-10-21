module

public import LeanSMILES.MachineLearning.Definitions

/-!
# Machine Learning — Executables

The `Float` side of the system. Every algorithm in `Definitions.lean` is written once
for a generic `[Scalar α]`:

* `α := ℝ` is what `Proofs.lean` proves things about (noncomputable);
* `α := Float` is what runs, through the definitions below.

Each definition here is the generic one at `α := Float` (the `*_eq` lemmas hold by
`rfl`), so a theorem about the generic definition is a theorem about the code that runs,
up to floating-point rounding. They exist because this module is precompiled. The
compiler specializes the generic code to `Float` here, once, so `#eval` in a notebook
calls fast native code instead of dictionary-passing generic code.

Open `ML.Exec` (rather than `ML`) to get the `Float` versions under the usual names.
-/

@[expose] public section

namespace ML.Exec

/-! ## Types -/

abbrev Vec (n : Nat) := Primitives.Vec Float n
abbrev Mat (m n : Nat) := Primitives.Mat Float m n
abbrev Dataset (m n : Nat) := ML.Dataset Float m n
abbrev LinearModel (n : Nat) := ML.LinearModel Float n
abbrev Objective (n : Nat) := Primitives.Objective Float n
abbrev GDConfig := Primitives.GDConfig Float
abbrev PerceptronConfig := Primitives.PerceptronConfig Float

variable {m n p : Nat}

/-! ## Linear algebra -/

def dot (u v : Vec n) : Float := Primitives.dot u v
def norm (v : Vec n) : Float := Primitives.norm v
def vadd (u v : Vec n) : Vec n := Primitives.vadd u v
def vsub (u v : Vec n) : Vec n := Primitives.vsub u v
def smul (c : Float) (v : Vec n) : Vec n := Primitives.smul c v
def matVec (A : Mat m n) (v : Vec n) : Vec m := Primitives.matVec A v
def matMul (A : Mat m n) (B : Mat n p) : Mat m p := Primitives.matMul A B
def transpose (A : Mat m n) : Mat n m := Primitives.transpose A
def colMean (X : Mat m n) : Vec n := Primitives.colMean X
def linSolve (A : Mat n n) (b : Vec n) : Vec n := Primitives.linSolve A b

/-! ## Linear models -/

def LinearModel.zero : LinearModel n := ML.LinearModel.zero
def LinearModel.score (model : LinearModel n) (x : Vec n) : Float := ML.LinearModel.score model x
def LinearModel.classify (model : LinearModel n) (x : Vec n) : Float :=
  ML.LinearModel.classify model x
def LinearModel.predictAll (model : LinearModel n) (X : Mat m n) : Vec m :=
  ML.LinearModel.predictAll model X

/-! ## Gradient descent -/

def gdStep (obj : Objective n) (η : Float) (w : Vec n) : Vec n := ML.gdStep obj η w

def gradientDescent (obj : Objective n) (cfg : GDConfig) (w₀ : Vec n) : Vec n :=
  ML.gradientDescent obj cfg w₀

def gradientDescentWithHistory (obj : Objective n) (cfg : GDConfig) (w₀ : Vec n)
    (every : Nat := 1) : Vec n × Array (Nat × Float) :=
  ML.gradientDescentWithHistory obj cfg w₀ every

/-! ## Linear regression -/

def mse (model : LinearModel n) (data : Dataset m n) : Float := ML.mse model data
def mseObjective (data : Dataset m n) : Objective (n + 1) := ML.mseObjective data
def olsFit (data : Dataset m n) : LinearModel n := ML.olsFit data
def linRegGD (cfg : GDConfig) (data : Dataset m n) : LinearModel n := ML.linRegGD cfg data

/-- `linRegGD` with a sparse design matrix: use it for fingerprint features. -/
def linRegGDSparse (cfg : GDConfig) (data : Dataset m n) : LinearModel n :=
  ML.linRegGDSparse cfg data

def linRegGDWithHistory (cfg : GDConfig) (data : Dataset m n) (every : Nat := 1) :
    LinearModel n × Array (Nat × Float) :=
  ML.linRegGDWithHistory cfg data every

/-! ## Perceptron -/

def perceptronLoss (model : LinearModel n) (x : Vec n) (y : Float) : Float :=
  ML.perceptronLoss model x y
def perceptronStep (η : Float) (model : LinearModel n) (x : Vec n) (y : Float) :
    LinearModel n :=
  ML.perceptronStep η model x y
def perceptronEpoch (η : Float) (data : Dataset m n) (model : LinearModel n) :
    LinearModel n :=
  ML.perceptronEpoch η data model
def perceptronFit (cfg : PerceptronConfig) (data : Dataset m n) : LinearModel n :=
  ML.perceptronFit cfg data

/-! ## The executed code is the generic code at `Float` -/

theorem olsFit_eq (data : Dataset m n) : olsFit data = ML.olsFit (α := Float) data := rfl
theorem linRegGD_eq (cfg : GDConfig) (data : Dataset m n) :
    linRegGD cfg data = ML.linRegGD (α := Float) cfg data := rfl
theorem linRegGDSparse_eq (cfg : GDConfig) (data : Dataset m n) :
    linRegGDSparse cfg data = ML.linRegGDSparse (α := Float) cfg data := rfl
theorem gradientDescent_eq (obj : Objective n) (cfg : GDConfig) (w₀ : Vec n) :
    gradientDescent obj cfg w₀ = ML.gradientDescent (α := Float) obj cfg w₀ := rfl
theorem perceptronFit_eq (cfg : PerceptronConfig) (data : Dataset m n) :
    perceptronFit cfg data = ML.perceptronFit (α := Float) cfg data := rfl

end ML.Exec

end
