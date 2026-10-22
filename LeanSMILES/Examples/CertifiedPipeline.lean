import LeanSMILES.Proofs.Certificates
import LeanSMILES.Float.Pipeline

/-!
# Certifying cheminformatics pipelines without training them

A pipeline is data + a molecular representation + a learning algorithm with its
hyperparameters. It is written once, for any `Scalar`:

* at `α := ℝ` we prove what the trained model is guaranteed to do, by filling in a
  *certificate*: a handful of conditions on the parameters, closed by `norm_num` or
  `decide`. **No training happens in any of these proofs.**
* at `α := Float` the same pipeline trains and predicts (`#eval`), which is optional.
  It shows numbers the guarantees bound.

Three pipelines:

1. solubility regression on Morgan fingerprints, by gradient descent;
2. the same on a matrix representation (adjacency matrix + normalized graph invariants);
3. a water-solubility classifier: a perceptron on radius-0 fingerprints, certified by an
   integer witness that the kernel checks.

Check this file with `lake build LeanSMILES.Examples.CertifiedPipeline`.
-/

open LeanSMILES Chem ML Primitives

set_option linter.hashCommand false

/-- A molecule from a SMILES string (the empty molecule if it does not parse). -/
def mol (s : String) : Molecule :=
  match (SMILES.mk s).parse with
  | .ok m => m
  | .error _ => default

/-- `mantissa · 10^exponent` in any `Scalar` (exact over `ℝ`). -/
def dec {α : Type} [Scalar α] (mantissa exponent : Int) : α :=
  (Decimal.mk mantissa exponent).toScalar

/-- Six molecules of the Delaney (ESOL) set with their measured log solubility. -/
def esolData (α : Type) [Scalar α] : LabelledMolecules α 6 where
  molecules := #v[mol "CCO", mol "c1ccccc1", mol "CCCCCC", mol "OCC(O)CO", mol "CC(=O)O",
    mol "Clc1ccccc1"]
  targets := #v[dec 2 (-2), dec (-164) (-2), dec (-384) (-2), dec 112 (-2), dec 122 (-2),
    dec (-238) (-2)]

/-! ## 1. Gradient descent on Morgan fingerprints -/

/-- Radius-2, 1024-bit Morgan fingerprints; gradient descent with step `1/2050` for
`41000` iterations. -/
def esolPipeline (α : Type) [Scalar α] : Pipeline α 6 1024 where
  data := esolData α
  representation := .morgan 2 1024
  algorithm := .gradientDescent ⟨1 / Scalar.fromNat 2050, 41000⟩

/-- The certificate. Fingerprint features are `0/1`, so `‖φ(mol)‖² ≤ 1024` for **every**
molecule (`morgan_bounded`); the remaining fields are arithmetic on the hyperparameters. -/
noncomputable def esolCertificate :
    Pipeline.GDCertificate (esolPipeline ℝ).representation ⟨1 / Scalar.fromNat 2050, 41000⟩ where
  R2 := (1024 : ℕ)
  B := 1
  ε := 1 / 20
  bounded := Representation.morgan_bounded 2 1024
  stepSize_pos := by norm_num
  stepSize_small := by norm_num -- 2 · (1/2050) · (1024 + 1) = 1
  iters_pos := by norm_num
  iters_enough := by norm_num -- 1 ≤ 2 · (1/2050) · 41000 · (1/20) = 2

/-- **Guarantee.** The trained model's training error is within `0.05` of that of every
linear model with `‖(w, b)‖² ≤ 1`. -/
theorem esol_guarantee (u : LinearModel ℝ 1024) (hu : normSq u.toParams ≤ 1) :
    (esolPipeline ℝ).trainMSE ≤ mse u (esolPipeline ℝ).dataset + 1 / 20 :=
  esolCertificate.sound (esolPipeline ℝ) rfl u hu

/-- The certificate never looked at the data, so the same guarantee holds for **every**
dataset of any size. -/
theorem esol_guarantee_any_data {m : ℕ} (data : LabelledMolecules ℝ m)
    (u : LinearModel ℝ 1024) (hu : normSq u.toParams ≤ 1) :
    ({ esolPipeline ℝ with data } : Pipeline ℝ m 1024).trainMSE ≤
      mse u ({ esolPipeline ℝ with data } : Pipeline ℝ m 1024).dataset + 1 / 20 :=
  esolCertificate.sound { esolPipeline ℝ with data } rfl u hu

/-- More iterations never increase the training error, under the same step size. -/
theorem esol_antitone :
    Antitone fun k => mse ((Algorithm.gradientDescent ⟨1 / Scalar.fromNat 2050, k⟩).fit
      (esolPipeline ℝ).dataset) (esolPipeline ℝ).dataset :=
  (esolPipeline ℝ).gd_antitone (by norm_num) esolCertificate.bounded
    esolCertificate.stepSize_small

/-- A pipeline that **fails** the certificate: with step `1/1000`, `2η(R² + 1) > 1`, so
gradient descent may diverge on some dataset and no guarantee is given. -/
example : ¬ 2 * (1 / 1000 : ℝ) * ((1024 : ℕ) + 1) ≤ 1 := by norm_num

-- The pipeline on `Float`: its training error (the quantity the guarantee bounds, up to
-- rounding) and its prediction for propan-1-ol (measured log solubility 0.62).
def esolModel : ML.Exec.LinearModel 1024 := Exec.Pipeline.model (esolPipeline Float)

#eval (Exec.Pipeline.trainMSE (esolPipeline Float),
  Exec.Pipeline.predictWith (esolPipeline Float) esolModel (mol "CCCO"))

/-! ## 2. A matrix representation -/

/-- The adjacency matrix of the first 8 atoms (64 bits) next to the normalized graph
invariants (atoms, bonds, Zagreb indices, Wiener index). -/
def graphPipeline (α : Type) [Scalar α] : Pipeline α 6 (8 * 8 + 5) where
  data := esolData α
  representation :=
    (Representation.adjacency 8 : Representation α (8 * 8)) ++
      (Representation.normalize .graphInvariants : Representation α 5)
  algorithm := .gradientDescent ⟨1 / Scalar.fromNat 132, 5000⟩

/-- The feature bound is the sum of the parts: `64` for the adjacency bits, `1` for the
normalized block. -/
noncomputable def graphCertificate :
    Pipeline.GDCertificate (graphPipeline ℝ).representation ⟨1 / Scalar.fromNat 132, 5000⟩ where
  R2 := ((8 : ℕ) : ℝ) * ((8 : ℕ) : ℝ) + 1
  B := 7
  ε := 1 / 10
  bounded := Representation.append_bounded (Representation.adjacency_bounded 8)
    (Representation.normalize_bounded _)
  stepSize_pos := by norm_num
  stepSize_small := by norm_num -- 2 · (1/132) · (65 + 1) = 1
  iters_pos := by norm_num
  iters_enough := by norm_num -- 7 ≤ 2 · (1/132) · 5000 · (1/10) ≈ 7.58

theorem graph_guarantee (u : LinearModel ℝ (8 * 8 + 5)) (hu : normSq u.toParams ≤ 7) :
    (graphPipeline ℝ).trainMSE ≤ mse u (graphPipeline ℝ).dataset + 1 / 10 :=
  graphCertificate.sound (graphPipeline ℝ) rfl u hu

def graphModel : ML.Exec.LinearModel (8 * 8 + 5) := Exec.Pipeline.model (graphPipeline Float)

#eval (Exec.Pipeline.trainMSE (graphPipeline Float),
  Exec.Pipeline.predictWith (graphPipeline Float) graphModel (mol "CCCO"))

/-! ## 3. A perceptron certified by an integer witness

Water-soluble (`+1`) against insoluble (`-1`) molecules, on radius-0, 64-bit Morgan
fingerprints. Bit 59 is the hydroxyl oxygen (`O` with one bond and one hydrogen), set in
exactly the soluble molecules. So the parameters `w₅₉ = 2`, bias `-1` score `+1` on soluble
molecules and `-1` on insoluble ones: a separator with margin `1`. Scaled by `3`,
‖(w, b)‖ = √5 / 3 ≤ 1. Each molecule sets at most 4 bits, so Novikoff's bound asks for
`(4 + 1) · 3² / 1² = 45` epochs.
-/

def solubleLabels : Vector ℤ 8 := #v[1, 1, 1, 1, -1, -1, -1, -1]

noncomputable def solubilityClassifier : Pipeline ℝ 8 64 where
  data :=
    { molecules := #v[mol "CCO", mol "OCC(O)CO", mol "CC(=O)O", mol "Oc1ccccc1",
        mol "CCCCCC", mol "c1ccccc1", mol "Clc1ccccc1", mol "Cc1ccccc1"]
      targets := solubleLabels.map (Int.cast : ℤ → ℝ) }
  representation := .morgan 0 64
  algorithm := .perceptron ⟨1, 45⟩

def hydroxylWitness : PerceptronWitness 64 where
  separator := Vector.ofFn fun j => if j.val = 59 then 2 else if j.val = 64 then -1 else 0
  scale := 3
  margin := 1
  maxBits := 4

/-- The kernel parses the SMILES, computes the fingerprints and checks the witness. -/
theorem hydroxylWitness_check :
    hydroxylWitness.check (fun m => (m.morganFingerprint 0 64).bits)
      solubilityClassifier.data.molecules solubleLabels 45 = true := by
  decide +kernel

noncomputable def solubilityCertificate :
    Pipeline.PerceptronCertificate solubilityClassifier ⟨1, 45⟩ :=
  hydroxylWitness.certificate solubilityClassifier rfl rfl (by norm_num) hydroxylWitness_check

/-- **Guarantee.** After 45 epochs the perceptron classifies every training molecule
correctly. -/
theorem solubility_guarantee (i : Fin 8) :
    solubilityClassifier.model.classify
        (solubilityClassifier.representation.featurize solubilityClassifier.data.molecules[i]) =
      solubilityClassifier.data.targets[i] :=
  solubilityCertificate.sound rfl i

theorem solubility_accuracy : solubilityClassifier.trainAccuracy = 1 :=
  solubilityCertificate.trainAccuracy_eq_one rfl (by norm_num)

/-- A witness that does **not** check: the weight is on bit 43 (aromatic carbon). -/
def aromaticWitness : PerceptronWitness 64 :=
  { hydroxylWitness with
    separator := Vector.ofFn fun j => if j.val = 43 then 2 else if j.val = 64 then -1 else 0 }

example :
    aromaticWitness.check (fun m => (m.morganFingerprint 0 64).bits)
      solubilityClassifier.data.molecules solubleLabels 45 = false := by
  decide +kernel
