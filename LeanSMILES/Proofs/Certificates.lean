/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/

module

public import LeanSMILES.Proofs.Pipeline
public import LeanSMILES.Polymorphic.Certificates

/-!
# Integer certificates — Soundness

`PerceptronWitness.certificate`: if `PerceptronWitness.check` returns `true` for a
pipeline on a bit representation, the pipeline has a `PerceptronCertificate`, so its
trained perceptron classifies every training molecule correctly
(`PerceptronCertificate.sound`). The check is a `Bool` computation over integers that the
kernel evaluates (`decide +kernel`), fingerprints included.

The bridge: over `ℝ`, `bitScore z bits = ⟪z, (x, 1)⟫`, `sqNorm z = ‖z‖²` and
`popCount bits = ‖x‖²`, where `x` is the `0/1` vector of `bits`.
-/

public section

namespace LeanSMILES

open Primitives Chem ML

namespace Check

variable {n : ℕ}

/-- The real vector of an integer vector. -/
abbrev toReal {k : ℕ} (z : Vector ℤ k) : Vec ℝ k := z.map (Int.cast : ℤ → ℝ)

/-- The `0/1` vector of a bit vector. -/
abbrev bitsToReal (bits : Vector Bool n) : Vec ℝ n := bits.map fun b => if b then 1 else 0

theorem bitScore_eq (z : Vector ℤ (n + 1)) (bits : Vector Bool n) :
    (bitScore z bits : ℝ) = dot (toReal z) (augment (bitsToReal bits)) := by
  rw [bitScore, foldl_add_eq_sum, zero_add, dot_eq_sum, Fin.sum_univ_castSucc]
  push_cast
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.getElem_fin, Fin.val_castSucc, Vector.getElem_map,
      augment_getElem_lt _ _ (by omega) j.isLt]
    split_ifs <;> simp
  · simp

theorem sqNorm_eq {k : ℕ} (z : Vector ℤ k) : (sqNorm z : ℝ) = normSq (toReal z) := by
  rw [sqNorm, foldl_add_eq_sum, zero_add, normSq_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by simp [sq]

theorem popCount_eq (bits : Vector Bool n) : (popCount bits : ℝ) = normSq (bitsToReal bits) := by
  rw [popCount, foldl_add_eq_sum, zero_add, normSq_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.getElem_fin, Vector.getElem_map]
  split_ifs <;> simp

end Check

theorem dot_smul_left {k : ℕ} (c : ℝ) (u v : Vec ℝ k) : dot (smul c u) v = c * dot u v := by
  simp only [dot_eq_sum, smul, Fin.getElem_fin, Vector.getElem_ofFn, Finset.mul_sum, mul_assoc]

/-- What a passing `check` says. -/
theorem PerceptronWitness.check_spec {m n : ℕ} {w : PerceptronWitness n}
    {bits : Molecule → Vector Bool n} {molecules : Vector Molecule m} {labels : Vector ℤ m}
    {epochs : ℕ} (h : w.check bits molecules labels epochs = true) :
    0 < w.scale ∧ 0 < w.margin ∧ Check.sqNorm w.separator ≤ (w.scale : ℤ) ^ 2 ∧
      (∀ i : Fin m, (labels[i] = 1 ∨ labels[i] = -1) ∧
        Check.popCount (bits molecules[i]) ≤ w.maxBits ∧
        w.margin ≤ labels[i] * Check.bitScore w.separator (bits molecules[i])) ∧
      ((w.maxBits + 1) * w.scale ^ 2 : ℤ) ≤ epochs * w.margin ^ 2 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hs, hg⟩, hnorm⟩, hall⟩, hep⟩ := h
  exact ⟨hs, hg, hnorm, fun i => ⟨(hall i).1.1, (hall i).1.2, (hall i).2⟩, hep⟩

/-- **Soundness of the integer check.** If `w.check` passes on a pipeline whose
representation is the bit representation `bits` and whose targets are the integer
labels, the pipeline has a perceptron certificate: its trained perceptron classifies
every training molecule correctly. -/
noncomputable def PerceptronWitness.certificate {m n : ℕ} (p : Pipeline ℝ m n)
    {bits : Molecule → Vector Bool n} (hrep : p.representation = .ofBits bits)
    {labels : Vector ℤ m} (htargets : p.data.targets = labels.map (Int.cast : ℤ → ℝ))
    {cfg : PerceptronConfig ℝ} (hη : 0 < cfg.learningRate) (w : PerceptronWitness n)
    (hcheck : w.check bits p.data.molecules labels cfg.epochs = true) :
    Pipeline.PerceptronCertificate p cfg :=
  have hspec := PerceptronWitness.check_spec hcheck
  have hs := hspec.1
  have hg := hspec.2.1
  have hnorm := hspec.2.2.1
  have hall := hspec.2.2.2.1
  have hep := hspec.2.2.2.2
  have hsR : (0 : ℝ) < w.scale := by exact_mod_cast hs
  have hgR : (0 : ℝ) < w.margin := by exact_mod_cast hg
  have hfeat : ∀ mol, p.representation.featurize mol = Check.bitsToReal (bits mol) := fun mol => by
    rw [hrep]; rfl
  have hy : ∀ i : Fin m, p.data.targets[i] = (labels[i] : ℝ) := fun i => by
    rw [htargets]; simp
  { R2 := w.maxBits
    bounded := fun i => by
      rw [hfeat, ← Check.popCount_eq]
      exact_mod_cast (hall i).2.1
    labels := fun i => by
      rw [hy]
      rcases (hall i).1 with h1 | h1 <;> simp [h1]
    separator := smul (1 / (w.scale : ℝ)) (Check.toReal w.separator)
    separator_norm := by
      rw [normSq_smul, ← Check.sqNorm_eq, div_pow, one_pow, one_div_mul_eq_div,
        div_le_one (by positivity)]
      exact_mod_cast hnorm
    γ := w.margin / w.scale
    margin_pos := by positivity
    margin := fun i => by
      rw [hy, hfeat, dot_smul_left, ← Check.bitScore_eq]
      have := (hall i).2.2
      set score := Check.bitScore w.separator (bits p.data.molecules[i])
      have hR : (w.margin : ℝ) ≤ labels[i] * score := by exact_mod_cast this
      rw [div_eq_mul_one_div, mul_comm (w.margin : ℝ)]
      calc 1 / (w.scale : ℝ) * w.margin ≤ 1 / (w.scale : ℝ) * (labels[i] * score) :=
            mul_le_mul_of_nonneg_left hR (by positivity)
        _ = _ := by ring
    rate_pos := hη
    epochs_enough := by
      have hR : ((w.maxBits + 1) * w.scale ^ 2 : ℝ) ≤ cfg.epochs * w.margin ^ 2 := by
        exact_mod_cast hep
      rw [div_le_iff₀ (by positivity), div_pow]
      calc ((w.maxBits : ℝ) + 1) = (w.maxBits + 1) * w.scale ^ 2 / w.scale ^ 2 := by
            field_simp
        _ ≤ cfg.epochs * w.margin ^ 2 / w.scale ^ 2 := by gcongr
        _ = cfg.epochs * (w.margin ^ 2 / w.scale ^ 2) := by ring }

end LeanSMILES

end
