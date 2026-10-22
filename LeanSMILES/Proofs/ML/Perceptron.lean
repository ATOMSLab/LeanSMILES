module

public import LeanSMILES.Proofs.ML.LeastSquares

/-!
# Perceptron — correctness and convergence

Write `xᵢ` for `augment data.X[i]` (the features with a `1` appended) and `θ` for a
model's parameters `model.toParams`, so that `model.score x = ⟪θ, augment x⟫`.

* **Counting** (`perceptronFitCounting_fst`): the counting variant trains the same model.
* **Stability** (`perceptronFit_stable`): once an epoch starts from a model that makes no
  mistakes, training never changes it again, and that model classifies every training
  example correctly (`classify_eq_of_not_isMistake`).
* **Novikoff's mistake bound** (`perceptron_mistake_bound`): if some `u` with `‖u‖ ≤ 1`
  separates the data with margin `γ > 0` and every `‖xᵢ‖ ≤ R`, the perceptron makes at
  most `(R/γ)²` updates in total, for any number of epochs.
* **Convergence** (`perceptron_converges`, `perceptron_classifies_of_le_epochs`): under
  the same assumptions, any number of epochs `≥ ⌊(R/γ)²⌋` classifies every training
  example correctly.
-/

public section

namespace ML

open Primitives

variable {m n : ℕ}

/-! ## Counting updates does not change the model -/

section Counting

variable {α : Type} [Scalar α]

/-- The update `perceptronEpochCounting` applies for sample `i`. -/
abbrev countingStep (η : α) (data : Dataset α m n) (s : LinearModel α n × ℕ) (i : Fin m) :
    LinearModel α n × ℕ :=
  if IsMistake s.1 data.X[i] data.y[i] then (perceptronStep η s.1 data.X[i] data.y[i], s.2 + 1)
  else s

theorem foldl_countingStep_fst (η : α) (data : Dataset α m n) (l : List (Fin m))
    (s : LinearModel α n × ℕ) :
    (l.foldl (countingStep η data) s).1 =
      l.foldl (fun model i => perceptronStep η model data.X[i] data.y[i]) s.1 := by
  induction l generalizing s with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    by_cases h : IsMistake s.1 data.X[i] data.y[i]
    · rw [countingStep, if_pos h]
    · rw [countingStep, if_neg h, perceptronStep_of_not_mistake _ _ _ _ h]

theorem perceptronEpochCounting_fst (η : α) (data : Dataset α m n) (s : LinearModel α n × ℕ) :
    (perceptronEpochCounting η data s).1 = perceptronEpoch η data s.1 :=
  foldl_countingStep_fst η data _ s

theorem iterate_perceptronEpochCounting_fst (η : α) (data : Dataset α m n) (k : ℕ)
    (s : LinearModel α n × ℕ) :
    (iterate (perceptronEpochCounting η data) k s).1 = iterate (perceptronEpoch η data) k s.1 := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact (ih _).trans (congrArg _ (perceptronEpochCounting_fst η data s))

/-- Counting updates does not change the trained model. -/
theorem perceptronFitCounting_fst (cfg : PerceptronConfig α) (data : Dataset α m n) :
    (perceptronFitCounting cfg data).1 = perceptronFit cfg data :=
  iterate_perceptronEpochCounting_fst _ data _ _

/-- The count never decreases within an epoch. -/
theorem foldl_countingStep_count_ge (η : α) (data : Dataset α m n) (l : List (Fin m))
    (s : LinearModel α n × ℕ) : s.2 ≤ (l.foldl (countingStep η data) s).2 := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons i l ih =>
    refine le_trans ?_ (ih (countingStep η data s i))
    by_cases h : IsMistake s.1 data.X[i] data.y[i]
    · rw [countingStep, if_pos h]; exact Nat.le_succ _
    · rw [countingStep, if_neg h]

/-- An epoch that makes no update started from a model with no mistakes on its samples. -/
theorem not_isMistake_of_count_eq (η : α) (data : Dataset α m n) (l : List (Fin m))
    (s : LinearModel α n × ℕ) (h : (l.foldl (countingStep η data) s).2 = s.2) :
    ∀ i ∈ l, ¬ IsMistake s.1 data.X[i] data.y[i] := by
  induction l generalizing s with
  | nil => simp
  | cons i l ih =>
    by_cases hi : IsMistake s.1 data.X[i] data.y[i]
    · exfalso
      have := foldl_countingStep_count_ge η data l (countingStep η data s i)
      simp only [List.foldl_cons] at h
      rw [countingStep, if_pos hi] at this
      rw [countingStep, if_pos hi] at h
      omega
    · have hs : countingStep η data s i = s := by rw [countingStep, if_neg hi]
      simp only [List.foldl_cons, hs] at h
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact ih s h j hj

/-- If the epoch's starting model misclassifies some sample, the epoch makes an update. -/
theorem perceptronEpochCounting_count_succ_le (η : α) (data : Dataset α m n)
    (s : LinearModel α n × ℕ) (h : ∃ i : Fin m, IsMistake s.1 data.X[i] data.y[i]) :
    s.2 + 1 ≤ (perceptronEpochCounting η data s).2 := by
  obtain ⟨i, hi⟩ := h
  have hge := foldl_countingStep_count_ge η data (List.finRange m) s
  by_contra hlt
  have heq : ((List.finRange m).foldl (countingStep η data) s).2 = s.2 := by
    change ¬ s.2 + 1 ≤ ((List.finRange m).foldl (countingStep η data) s).2 at hlt
    omega
  exact not_isMistake_of_count_eq η data _ s heq i (List.mem_finRange i) hi

end Counting

/-! ## Stability -/

section Stability

variable {α : Type} [Scalar α]

/-- An epoch from a model that makes no mistake on any sample leaves it unchanged. -/
theorem perceptronEpoch_eq_self (η : α) (data : Dataset α m n) (model : LinearModel α n)
    (h : ∀ i : Fin m, ¬ IsMistake model data.X[i] data.y[i]) :
    perceptronEpoch η data model = model := by
  unfold perceptronEpoch
  suffices ∀ l : List (Fin m),
      l.foldl (fun model i => perceptronStep η model data.X[i] data.y[i]) model = model from
    this _
  intro l
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons, perceptronStep_of_not_mistake _ _ _ _ (h i)]
    exact ih

theorem perceptronFit_add (η : α) (data : Dataset α m n) (k j : ℕ) :
    perceptronFit ⟨η, k + j⟩ data =
      iterate (perceptronEpoch η data) j (perceptronFit ⟨η, k⟩ data) := by
  simp only [perceptronFit, iterate_eq_iterate]
  rw [add_comm, Function.iterate_add_apply]

/-- **Stability**: once the model after `k` epochs makes no mistakes, further epochs never
change it. -/
theorem perceptronFit_stable (η : α) (data : Dataset α m n) (k : ℕ)
    (h : ∀ i : Fin m, ¬ IsMistake (perceptronFit ⟨η, k⟩ data) data.X[i] data.y[i]) (j : ℕ) :
    perceptronFit ⟨η, k + j⟩ data = perceptronFit ⟨η, k⟩ data := by
  rw [perceptronFit_add]
  induction j with
  | zero => rfl
  | succ j ih => rw [iterate_succ', ih, perceptronEpoch_eq_self _ _ _ h]

end Stability

/-! ## Classification over `ℝ` -/

section Classification

/-- With `±1` labels, a sample that is not a mistake is classified correctly. -/
theorem classify_eq_of_not_isMistake (model : LinearModel ℝ n) (x : Vec ℝ n) {y : ℝ}
    (hy : y = 1 ∨ y = -1) (h : ¬ IsMistake model x y) : model.classify x = y := by
  unfold IsMistake at h
  push Not at h
  unfold LinearModel.classify
  rcases hy with rfl | rfl
  · rw [if_pos (by linarith)]
  · rw [if_neg (by linarith)]

/-- Conversely, a misclassified sample is a mistake. -/
theorem isMistake_of_classify_ne (model : LinearModel ℝ n) (x : Vec ℝ n) {y : ℝ}
    (hy : y = 1 ∨ y = -1) (h : model.classify x ≠ y) : IsMistake model x y := by
  by_contra h'
  exact h (classify_eq_of_not_isMistake model x hy h')

end Classification

/-! ## Novikoff's mistake bound -/

section Novikoff

variable (data : Dataset ℝ m n)

theorem score_eq_dot_toParams (model : LinearModel ℝ n) (x : Vec ℝ n) :
    model.score x = dot model.toParams (augment x) := by
  rw [← score_ofParams, ofParams_toParams]

/-- On a mistake the parameters move by `η y xᵢ`. -/
theorem toParams_perceptronStep (η : ℝ) (model : LinearModel ℝ n) (x : Vec ℝ n) (y : ℝ)
    (h : IsMistake model x y) :
    (perceptronStep η model x y).toParams = vadd model.toParams (smul (η * y) (augment x)) := by
  rw [perceptronStep_of_mistake η model x y h]
  ext j hj
  by_cases hjn : j < n
  · simp [LinearModel.toParams, vadd, smul, augment, Vector.getElem_push, hjn]
  · have : j = n := by omega
    subst this
    simp [LinearModel.toParams, vadd, smul, augment, Vector.getElem_push]

theorem toParams_zero : (LinearModel.zero : LinearModel ℝ n).toParams = vzero := by
  ext j hj
  by_cases hjn : j < n <;>
    simp [LinearModel.zero, LinearModel.toParams, vzero, Vector.getElem_push, hjn]

theorem dot_vzero {k : ℕ} (u : Vec ℝ k) : dot u vzero = 0 := by
  simp [dot_eq_sum, vzero]

/-- The invariant behind Novikoff's bound, after `s.2` updates:
`⟪u, θ⟫ ≥ s.2 η γ` and `‖θ‖² ≤ s.2 η² R²`. -/
def NovikoffInv (η γ R : ℝ) (u : Vec ℝ (n + 1)) (s : LinearModel ℝ n × ℕ) : Prop :=
  (s.2 : ℝ) * η * γ ≤ dot u s.1.toParams ∧ normSq s.1.toParams ≤ s.2 * η ^ 2 * R ^ 2

theorem novikoffInv_zero (η γ R : ℝ) (u : Vec ℝ (n + 1)) :
    NovikoffInv η γ R u (LinearModel.zero, 0) := by
  simp [NovikoffInv, toParams_zero, dot_vzero, normSq]

/-- One `countingStep` preserves the invariant: an update raises `⟪u, θ⟫` by at least
`ηγ` (margin) and `‖θ‖²` by at most `η²R²` (it was a mistake, so the cross term is
`≤ 0`). -/
theorem novikoffInv_step {η γ R : ℝ} (hη : 0 ≤ η) {u : Vec ℝ (n + 1)} (i : Fin m)
    (hy : data.y[i] = 1 ∨ data.y[i] = -1)
    (hmargin : γ ≤ data.y[i] * dot u (augment data.X[i]))
    (hR : normSq (augment data.X[i]) ≤ R ^ 2)
    {s : LinearModel ℝ n × ℕ} (hs : NovikoffInv η γ R u s) :
    NovikoffInv η γ R u (countingStep η data s i) := by
  by_cases h : IsMistake s.1 data.X[i] data.y[i]
  · rw [countingStep, if_pos h]
    obtain ⟨h1, h2⟩ := hs
    have hy2 : data.y[i] ^ 2 = 1 := by rcases hy with h | h <;> rw [h] <;> norm_num
    have hmist : data.y[i] * dot s.1.toParams (augment data.X[i]) ≤ 0 := by
      have h' := h
      unfold IsMistake at h'
      rwa [score_eq_dot_toParams] at h'
    refine ⟨?_, ?_⟩
    · simp only [toParams_perceptronStep η s.1 _ _ h, dot_vadd_smul]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hmargin hη]
    · simp only [toParams_perceptronStep η s.1 _ _ h, normSq_vadd_smul]
      push_cast
      have hsq : (η * data.y[i]) ^ 2 = η ^ 2 := by rw [mul_pow, hy2, mul_one]
      rw [hsq]
      nlinarith [mul_le_mul_of_nonneg_left hR (sq_nonneg η),
        mul_nonpos_of_nonneg_of_nonpos hη hmist]
  · rw [countingStep, if_neg h]
    exact hs

theorem novikoffInv_fit {η γ R : ℝ} (hη : 0 ≤ η) {u : Vec ℝ (n + 1)}
    (hy : ∀ i : Fin m, data.y[i] = 1 ∨ data.y[i] = -1)
    (hmargin : ∀ i : Fin m, γ ≤ data.y[i] * dot u (augment data.X[i]))
    (hR : ∀ i : Fin m, normSq (augment data.X[i]) ≤ R ^ 2) (epochs : ℕ) :
    NovikoffInv η γ R u (perceptronFitCounting ⟨η, epochs⟩ data) := by
  have hepoch : ∀ s, NovikoffInv η γ R u s →
      NovikoffInv η γ R u (perceptronEpochCounting η data s) := by
    intro s hs
    change NovikoffInv η γ R u ((List.finRange m).foldl (countingStep η data) s)
    suffices ∀ (l : List (Fin m)) s, NovikoffInv η γ R u s →
        NovikoffInv η γ R u (l.foldl (countingStep η data) s) from this _ s hs
    intro l
    induction l with
    | nil => exact fun s hs => hs
    | cons i l ih =>
      exact fun s hs => ih _ (novikoffInv_step data hη i (hy i) (hmargin i) (hR i) hs)
  unfold perceptronFitCounting
  suffices ∀ (k : ℕ) s, NovikoffInv η γ R u s →
      NovikoffInv η γ R u (iterate (perceptronEpochCounting η data) k s) from
    this epochs _ (novikoffInv_zero η γ R u)
  intro k
  induction k with
  | zero => exact fun s hs => hs
  | succ k ih => exact fun s hs => ih _ (hepoch s hs)

/-- **Novikoff's mistake bound.** Suppose the labels are `±1`, a vector `u` with `‖u‖ ≤ 1`
(in the augmented space, so it includes a bias) separates the data with margin `γ > 0`, and every
augmented sample has `‖xᵢ‖ ≤ R`. Then however many epochs it runs, the perceptron makes
at most `(R/γ)²` updates: `mistakes · γ² ≤ R²`. -/
theorem perceptron_mistake_bound {η γ R : ℝ} (hη : 0 < η)
    (hy : ∀ i : Fin m, data.y[i] = 1 ∨ data.y[i] = -1)
    (u : Vec ℝ (n + 1)) (hu : normSq u ≤ 1)
    (hmargin : ∀ i : Fin m, γ ≤ data.y[i] * dot u (augment data.X[i]))
    (hγ : 0 < γ) (hR : ∀ i : Fin m, normSq (augment data.X[i]) ≤ R ^ 2) (epochs : ℕ) :
    ((perceptronFitCounting ⟨η, epochs⟩ data).2 : ℝ) * γ ^ 2 ≤ R ^ 2 := by
  obtain ⟨h1, h2⟩ := novikoffInv_fit data hη.le hy hmargin hR epochs
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (perceptronFitCounting ⟨η, epochs⟩ data).2 := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = (perceptronFitCounting ⟨η, epochs⟩ data).1.toParams := ⟨_, rfl⟩
  rw [← hk, ← hθ] at h1 h2
  rw [← hk]
  have hcs : dot u θ ^ 2 ≤ normSq θ :=
    (dot_sq_le u θ).trans (mul_le_of_le_one_left (normSq_nonneg θ) hu)
  have hk0 : 0 ≤ k := hk ▸ Nat.cast_nonneg _
  have hpos : 0 ≤ k * η * γ := by positivity
  -- `(kηγ)² ≤ ⟪u, θ⟫² ≤ ‖θ‖² ≤ kη²R²` (Cauchy–Schwarz with `‖u‖ ≤ 1`)
  have hsq : (k * η * γ) ^ 2 ≤ k * η ^ 2 * R ^ 2 :=
    (pow_le_pow_left₀ hpos h1 2).trans (hcs.trans h2)
  rcases hk0.eq_or_lt with h0 | hkpos
  · rw [← h0, zero_mul]
    positivity
  · have hc : 0 < k * η ^ 2 := by positivity
    refine le_of_mul_le_mul_left ?_ hc
    calc k * η ^ 2 * (k * γ ^ 2) = (k * η * γ) ^ 2 := by ring
      _ ≤ k * η ^ 2 * R ^ 2 := hsq

/-- The mistake bound as a division: at most `R² / γ²` updates. -/
theorem perceptron_mistakes_le {η γ R : ℝ} (hη : 0 < η)
    (hy : ∀ i : Fin m, data.y[i] = 1 ∨ data.y[i] = -1)
    (u : Vec ℝ (n + 1)) (hu : normSq u ≤ 1)
    (hmargin : ∀ i : Fin m, γ ≤ data.y[i] * dot u (augment data.X[i]))
    (hγ : 0 < γ) (hR : ∀ i : Fin m, normSq (augment data.X[i]) ≤ R ^ 2) (epochs : ℕ) :
    ((perceptronFitCounting ⟨η, epochs⟩ data).2 : ℝ) ≤ R ^ 2 / γ ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  exact perceptron_mistake_bound data hη hy u hu hmargin hγ hR epochs

/-- **Convergence.** Under the assumptions of the mistake bound, some `k ≤ ⌊(R/γ)²⌋`
epochs give a model that classifies every training example correctly; by
`perceptronFit_stable`, training longer keeps that model. -/
theorem perceptron_converges {η γ R : ℝ} (hη : 0 < η)
    (hy : ∀ i : Fin m, data.y[i] = 1 ∨ data.y[i] = -1)
    (u : Vec ℝ (n + 1)) (hu : normSq u ≤ 1)
    (hmargin : ∀ i : Fin m, γ ≤ data.y[i] * dot u (augment data.X[i]))
    (hγ : 0 < γ) (hR : ∀ i : Fin m, normSq (augment data.X[i]) ≤ R ^ 2) :
    ∃ k ≤ ⌊R ^ 2 / γ ^ 2⌋₊, ∀ i : Fin m,
      ¬ IsMistake (perceptronFit ⟨η, k⟩ data) data.X[i] data.y[i] := by
  by_contra hcon
  push Not at hcon
  set N := ⌊R ^ 2 / γ ^ 2⌋₊
  -- every epoch up to `N` starts from a model with a mistake, so each one makes an update
  have hcount : ∀ k ≤ N + 1, k ≤ (perceptronFitCounting ⟨η, k⟩ data).2 := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hfst : (perceptronFitCounting ⟨η, k⟩ data).1 = perceptronFit ⟨η, k⟩ data :=
        perceptronFitCounting_fst _ data
      have hstep : (perceptronFitCounting ⟨η, k + 1⟩ data) =
          perceptronEpochCounting η data (perceptronFitCounting ⟨η, k⟩ data) := by
        unfold perceptronFitCounting
        exact iterate_succ' _ _ _
      obtain ⟨i, hi⟩ := hcon k (by omega)
      have := perceptronEpochCounting_count_succ_le η data (perceptronFitCounting ⟨η, k⟩ data)
        ⟨i, hfst ▸ hi⟩
      rw [hstep]
      have := ih (by omega)
      omega
  have hge := hcount (N + 1) le_rfl
  have hle := perceptron_mistakes_le data hη hy u hu hmargin hγ hR (N + 1)
  have hlt := Nat.lt_floor_add_one (R ^ 2 / γ ^ 2)
  have : ((N + 1 : ℕ) : ℝ) ≤ (perceptronFitCounting ⟨η, N + 1⟩ data).2 := by
    exact_mod_cast hge
  push_cast at this
  linarith

/-- After convergence, the perceptron classifies every training example correctly, and
keeps doing so for any number of further epochs. -/
theorem perceptron_classifies_training_set {η γ R : ℝ} (hη : 0 < η)
    (hy : ∀ i : Fin m, data.y[i] = 1 ∨ data.y[i] = -1)
    (u : Vec ℝ (n + 1)) (hu : normSq u ≤ 1)
    (hmargin : ∀ i : Fin m, γ ≤ data.y[i] * dot u (augment data.X[i]))
    (hγ : 0 < γ) (hR : ∀ i : Fin m, normSq (augment data.X[i]) ≤ R ^ 2) :
    ∃ k ≤ ⌊R ^ 2 / γ ^ 2⌋₊, ∀ j : ℕ, ∀ i : Fin m,
      (perceptronFit ⟨η, k + j⟩ data).classify data.X[i] = data.y[i] := by
  obtain ⟨k, hk, hclean⟩ := perceptron_converges data hη hy u hu hmargin hγ hR
  refine ⟨k, hk, fun j i => ?_⟩
  rw [perceptronFit_stable η data k hclean j]
  exact classify_eq_of_not_isMistake _ _ (hy i) (hclean i)

/-- **Convergence, for a given epoch budget.** Under the assumptions of the mistake bound,
every number of epochs `E ≥ ⌊(R/γ)²⌋` gives a model that classifies every training
example correctly. This is checkable before training: it only involves `E`, `R` and
`γ`. -/
theorem perceptron_classifies_of_le_epochs {η γ R : ℝ} (hη : 0 < η)
    (hy : ∀ i : Fin m, data.y[i] = 1 ∨ data.y[i] = -1)
    (u : Vec ℝ (n + 1)) (hu : normSq u ≤ 1)
    (hmargin : ∀ i : Fin m, γ ≤ data.y[i] * dot u (augment data.X[i]))
    (hγ : 0 < γ) (hR : ∀ i : Fin m, normSq (augment data.X[i]) ≤ R ^ 2) {E : ℕ}
    (hE : ⌊R ^ 2 / γ ^ 2⌋₊ ≤ E) (i : Fin m) :
    (perceptronFit ⟨η, E⟩ data).classify data.X[i] = data.y[i] := by
  obtain ⟨k, hk, hclean⟩ := perceptron_classifies_training_set data hη hy u hu hmargin hγ hR
  obtain ⟨j, rfl⟩ : ∃ j, E = k + j := ⟨E - k, by omega⟩
  exact hclean j i

end Novikoff

end ML

end
