/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
import LeanSMILES.Proofs.Pipeline.Certificates

/-!
# Certifying linear-regression pipelines without training them

A pipeline is labelled molecules (SMILES + exact targets), a molecular representation from
the SMILES toolkit, a ridge penalty `λ`, and an iterative solver with its hyperparameters.
For each solver there is a certificate: conditions checked **without training**, and a
theorem that turns them into a guarantee about the trained model.

1. **Gradient descent on Morgan fingerprints.** The conditions mention only the
   representation and the hyperparameters, so `norm_num` checks them and the guarantee
   holds for every dataset.
2. **Jacobi and Gauss–Seidel on bond-order matrices.** The condition (weighted diagonal
   dominance of the normal equations) is about the data. The kernel checks it exactly:
   it parses the SMILES, builds the matrices and solves nothing.
3. **What fails**: a step size too large for the representation, and Jacobi without
   enough ridge penalty, which the check rejects (and which indeed diverges on `Float`).

Check this file with `lake build LeanSMILES.Examples.CertifiedPipeline`.
-/

open LeanSMILES Regression

set_option linter.hashCommand false

/-- Labelled molecules from `(SMILES, target)` pairs (all must parse). -/
def labelled {m : ℕ} (entries : Vector (String × ℚ) m) : LabelledMolecules m :=
  match LabelledMolecules.ofSmiles entries with
  | .ok D => D
  | .error _ => ⟨Vector.replicate m Mol.empty, Vector.replicate m 0⟩

/-! ## 1. Gradient descent on Morgan fingerprints -/

/-- Six molecules of the Delaney (ESOL) set with their measured log solubility. -/
def esol : LabelledMolecules 6 := labelled
  #v[("CCO", 2 / 100), ("c1ccccc1", -164 / 100), ("CCCCCC", -384 / 100),
    ("OCC(O)CO", 112 / 100), ("CC(=O)O", 122 / 100), ("Clc1ccccc1", -238 / 100)]

/-- Radius-2, 64-bit Morgan fingerprints; gradient descent with step `1/130` for 2600 steps. -/
def esolGD : Pipeline 6 64 :=
  { data := esol, representation := .morgan 2 64, algorithm := .gradientDescent (1 / 130) 2600 }

/-- The certificate. Fingerprint features are `0/1`, so `‖φ(M)‖² ≤ 64` for **every**
molecule (`morgan_bounded`); the other fields are arithmetic on `λ = 0`, `η = 1/130`,
`k = 2600`. -/
def esolCertificate : GDCertificate (Representation.morgan 2 64) 0 (1 / 130) 2600 where
  R2 := (64 : ℕ)
  B := 4
  ε := 1 / 10
  bounded := Representation.morgan_bounded 2 64
  ridge_nonneg := le_rfl
  stepSize_pos := by norm_num
  stepSize_small := by norm_num -- 2 · (1/130) · (64 + 1 + 0) = 1
  iters_pos := by norm_num
  iters_enough := by norm_num -- 4 ≤ 2 · (1/130) · 2600 · (1/10) = 4

/-- **Guarantee.** The trained model's training loss is within `0.1` of that of every
parameter vector with `‖(w, b)‖² ≤ 4`. -/
theorem esol_guarantee (u : Vec ℝ 65) (hu : ∑ i : Fin 65, u[i] ^ 2 ≤ 4) :
    esolGD.trainLoss ℝ ≤ (esolGD.problem ℝ).loss u + 1 / 10 := by
  have := esolCertificate.sound esolGD rfl rfl rfl u hu
  simpa [esolCertificate] using this

/-- The certificate never looked at the data: the same guarantee for **every** dataset. -/
theorem esol_guarantee_any_data {m : ℕ} (data : LabelledMolecules m) (u : Vec ℝ 65)
    (hu : ∑ i : Fin 65, u[i] ^ 2 ≤ 4) :
    ({ esolGD with data } : Pipeline m 64).trainLoss ℝ ≤
      (({ esolGD with data } : Pipeline m 64).problem ℝ).loss u + 1 / 10 := by
  have := esolCertificate.sound { esolGD with data } rfl rfl rfl u hu
  simpa [esolCertificate] using this

/-- A step size that **fails** the certificate: with `η = 1/50`, `2η(R² + 1) > 1`. -/
example : ¬ 2 * (1 / 50 : ℚ) * ((64 : ℕ) + 1 + 0) ≤ 1 := by norm_num

-- The same pipeline runs on `Float`: its training loss, and its prediction for propan-1-ol
-- (measured log solubility 0.62).
#eval (esolGD.trainLoss Float, esolGD.predictWith (esolGD.model Float) (Mol.ofSmiles! "CCCO"))

/-! ## 2. Jacobi and Gauss–Seidel on bond-order matrices -/

/-- Four small molecules with log solubility values. -/
def small : LabelledMolecules 4 := labelled
  #v[("CCO", -77 / 100), ("CC=O", 64 / 100), ("CCC", -94 / 100), ("OCO", 1)]

/-- The bond-order matrix of the first 3 atoms, ridge penalty `λ = 8`, 40 Jacobi steps. -/
def smallJacobi : Pipeline 4 9 :=
  { data := small, representation := .bondOrders 3, ridge := 8, algorithm := .jacobi 40 }

/-- The same with 40 Gauss–Seidel sweeps. -/
def smallGaussSeidel : Pipeline 4 9 := { smallJacobi with algorithm := .gaussSeidel 40 }

-- The proposed witness: unit weights, `ρ = 22/39`, `β = 57/1700`; the excess loss it
-- certifies after 40 iterations is below `10⁻¹⁷`.
#eval (smallJacobi.suggestWitness,
  decide (smallJacobi.certifiedExcess smallJacobi.suggestWitness < 1 / 10 ^ 17))

/-- **The kernel checks the certificate**: it parses the SMILES, builds the bond-order
matrices, forms the normal equations exactly and verifies diagonal dominance. -/
theorem smallJacobi_check :
    smallJacobi.checkSolver smallJacobi.suggestWitness (1 / 1000) = true := by
  decide +kernel

theorem smallGaussSeidel_check :
    smallGaussSeidel.checkSolver smallGaussSeidel.suggestWitness (1 / 1000) = true := by
  decide +kernel

/-- **Guarantee.** After 40 Jacobi steps, the trained model is within `0.001` of the
optimum of the ridge loss: no parameter vector does better by more than that. -/
theorem smallJacobi_guarantee (u : Vec ℝ 10) :
    smallJacobi.trainLoss ℝ ≤ (smallJacobi.problem ℝ).loss u + 1 / 1000 := by
  have := smallJacobi.checkSolver_sound smallJacobi_check u
  simpa using this

theorem smallGaussSeidel_guarantee (u : Vec ℝ 10) :
    smallGaussSeidel.trainLoss ℝ ≤ (smallGaussSeidel.problem ℝ).loss u + 1 / 1000 := by
  have := smallGaussSeidel.checkSolver_sound smallGaussSeidel_check u
  simpa using this

/-- Gauss–Seidel needs no certificate to be monotone: more sweeps never increase the
loss, for any data. -/
example : Antitone fun k => (smallGaussSeidel.problem ℝ).loss
    (gaussSeidel (smallGaussSeidel.problem ℝ).normalMatrix
      (smallGaussSeidel.problem ℝ).normalVector k) :=
  smallGaussSeidel.gaussSeidel_antitone (by norm_num [smallGaussSeidel, smallJacobi])

#eval (smallJacobi.trainLoss Float, smallGaussSeidel.trainLoss Float)

/-! ## 3. What the check rejects -/

/-- Without the ridge penalty the normal equations are not diagonally dominant, and the
check fails. -/
def smallJacobiOLS : Pipeline 4 9 := { smallJacobi with ridge := 0 }

example : smallJacobiOLS.checkSolver smallJacobiOLS.suggestWitness 1 = false := by
  decide +kernel

/-- On the six ESOL molecules with `λ = 5` the Jacobi check fails. -/
def esolJacobi : Pipeline 6 16 :=
  { data := esol, representation := .bondOrders 4, ridge := 5, algorithm := .jacobi 50 }

-- The check fails; Jacobi indeed diverges on `Float`, while Gauss–Seidel (monotone for any
-- data) settles.
#eval (esolJacobi.checkSolver esolJacobi.suggestWitness 1,
  esolJacobi.trainLoss Float, ({ esolJacobi with algorithm := .gaussSeidel 50 }).trainLoss Float)

/-! ## Molecules, not SMILES spellings -/

-- The data's canonical SMILES (the toolkit's), and the check that no molecule occurs twice,
-- however it was spelled.
#eval (esol.canonicalSmiles, esol.noDuplicates)

/-- A canonical representation gives every atom numbering of a molecule the same
features. -/
example (M : Mol) (σ : Equiv.Perm (Fin M.n)) :
    Representation.canonical (Representation.bondOrders 4) (M.relabel σ) =
      Representation.canonical (Representation.bondOrders 4) M :=
  Representation.canonical_relabel _ M σ
