/-
Copyright (c) 2026 TorchLean
Released under MIT license as described in the file LICENSES/TorchLean-MIT.txt.
Authors: TorchLean Team
-/

module

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Algorithmic stability (learning theory)

This file defines the vocabulary for algorithmic stability: datasets, replace-one and
remove-one perturbations, empirical error, deterministic replace-one uniform stability
(`UniformStableReplace`), and IID sampling of datasets.

The goal here is to provide a small, reusable vocabulary that downstream developments can reuse.
The definitions follow the standard event-wise / test-point-wise inequalities from the literature,
stated in a way that is easy to connect to concrete algorithms and bounds.

We keep the definitions general and avoid committing to a particular hypothesis class structure:
stability is useful both for classical ERM analyses and for modern training procedures, and the
right ambient structure depends on the application.

## Scope and design notes

### Datasets as functions

We represent a dataset of size `n` as a function `Dataset n Z := Fin n → Z`, so the
“dataset has exactly `n` elements” invariant is enforced by the type.

What matters for stability is that we can (a) access coordinate `i : Fin n` and (b) perform
replace-one / remove-one perturbations; `Dataset.get`, `replaceAt` and `removeAt` are the
interface the proofs use. This file holds definitions only. Concrete bounds are proved in
separate files, e.g. `LeanSMILES.LearningTheory.Stability.RidgeRegression1D`.

### Measures and expectations

For sampling, we assume `[MeasurableSpace Z]` and use mathlib's `ProbabilityMeasure`:
`iid μ n` is the product distribution on datasets `S : Dataset n Z`.

## References

Algorithmic stability is a standard toolbox for generalization bounds. Classic and modern
references include:

- Bousquet & Elisseeff (2002), “Stability and Generalization”.
- Shalev-Shwartz et al. (2010), “Learnability, Stability and Uniform Convergence”.
- Hardt, Recht & Singer (2016), “Train faster, generalize better: Stability of stochastic gradient
  descent”.
- For a textbook perspective relating stability, uniform convergence, and generalization, see
  Shalev-Shwartz & Ben-David (2014), “Understanding Machine Learning: From Theory to Algorithms”.

## Provenance

Extracted from TorchLean (`NN/MLTheory/LearningTheory/Stability/Core.lean`, `main` at `772b6b8`),
MIT-licensed; see `LICENSES/TorchLean-MIT.txt`. The one structural change: TorchLean's `Dataset` is
its shape-indexed `TorchLean.Tensor Z [n]`, moved to and from functions by `Tensor.vectorEquiv`;
LeanSMILES has no tensor type, so `Dataset n Z` is `Fin n → Z` itself. `toFn` and `ofFn` are kept
(as the identity) so downstream proofs port unchanged, and the transported `MeasurableSpace`
instance is dropped because the product instance on `Fin n → Z` already applies.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LeanSMILES.LearningTheory.Stability

variable {Z H : Type}

/-! ## Datasets -/

/--
A dataset of size `n` with examples in `Z`.

The sample count is recorded in the type.
-/
abbrev Dataset (n : Nat) (Z : Type) : Type :=
  Fin n → Z

namespace Dataset

variable {n : Nat} {Z : Type}

/-- View a dataset as a function `Fin n → Z` (the identity, kept as a named interface). -/
abbrev toFn (S : Dataset n Z) : Fin n → Z :=
  S

/-- Build a dataset from a function `Fin n → Z` (the identity, kept as a named interface). -/
abbrev ofFn (f : Fin n → Z) : Dataset n Z :=
  f

/-- Reading back a dataset built from a function recovers the function. (Not `@[simp]`: with
`Dataset n Z := Fin n → Z` both sides are syntactically `f` after unfolding.) -/
theorem toFn_ofFn (f : Fin n → Z) :
    toFn (n := n) (Z := Z) (ofFn (n := n) (Z := Z) f) = f :=
  rfl

/-- The other round trip. -/
theorem ofFn_toFn (S : Dataset n Z) :
    ofFn (n := n) (Z := Z) (toFn (n := n) (Z := Z) S) = S :=
  rfl

/-- Coordinate access for datasets. -/
abbrev get (S : Dataset n Z) (i : Fin n) : Z :=
  toFn (n := n) (Z := Z) S i

/-- Coordinate access on a dataset built from a function is just application. -/
@[simp] theorem get_ofFn (f : Fin n → Z) (i : Fin n) :
    get (n := n) (Z := Z) (ofFn (n := n) (Z := Z) f) i = f i :=
  rfl

section Measure

variable [MeasurableSpace Z]

/-- `toFn` is measurable (it is the identity on the product measurable space). -/
theorem measurable_toFn : Measurable (toFn (n := n) (Z := Z) : Dataset n Z → (Fin n → Z)) :=
  measurable_id

/-- `ofFn` is measurable (it is the identity on the product measurable space). -/
theorem measurable_ofFn : Measurable (ofFn (n := n) (Z := Z) : (Fin n → Z) → Dataset n Z) :=
  measurable_id

end Measure

end Dataset

/--
Replace the example at index `i` with `z'`.

This is the standard “replace-one” perturbation used in uniform stability definitions.
-/
def replaceAt {n : Nat} (S : Dataset n Z) (i : Fin n) (z' : Z) : Dataset n Z :=
  Dataset.ofFn (n := n) (Z := Z) (Function.update (Dataset.toFn (n := n) (Z := Z) S) i z')

/-- Reading a replaced dataset returns the replacement at that coordinate and the original
example everywhere else. -/
@[simp] theorem get_replaceAt {n : Nat} (S : Dataset n Z) (i j : Fin n) (z' : Z) :
    Dataset.get (replaceAt S i z') j = if j = i then z' else Dataset.get S j := by
  rw [replaceAt, Dataset.get_ofFn]
  exact Function.update_apply _ _ _ _

/--
Remove the example at index `i` from a dataset of size `n+1`.

This uses `Fin.succAbove` to reindex the remaining elements into `Fin n`.
-/
def removeAt {n : Nat} (S : Dataset (n + 1) Z) (i : Fin (n + 1)) : Dataset n Z :=
  Dataset.ofFn (n := n) (Z := Z) (fun j => Dataset.get (n := n + 1) (Z := Z) S (i.succAbove j))

/-- Reading a shortened dataset skips the removed index, which is what `Fin.succAbove` encodes. -/
@[simp] theorem get_removeAt {n : Nat} (S : Dataset (n + 1) Z) (i : Fin (n + 1)) (j : Fin n) :
    Dataset.get (removeAt S i) j = Dataset.get S (i.succAbove j) := by
  exact Dataset.get_ofFn _ _

/-! ## Learning algorithms and loss -/

/--
A deterministic learning algorithm mapping datasets to hypotheses.

This is the interface needed to state stability: an “algorithm” is just a function
`Dataset n Z → H`.
-/
abbrev LearningMap (n : Nat) (Z H : Type) : Type :=
  Dataset n Z → H

/--
A real-valued loss function.

We fix the codomain to `ℝ` to match the standard stability literature.
-/
abbrev Loss (H Z : Type) : Type :=
  H → Z → ℝ

/-! ## Errors -/

/--
Empirical error (average loss on a dataset).

We write this with an explicit $1/n$ normalization so downstream lemmas can control constants.
At `n = 0`, the totalized real expression is zero.
-/
def empiricalError {n : Nat} (ℓ : Loss H Z) (h : H) (S : Dataset n Z) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, ℓ h (Dataset.get (n := n) (Z := Z) S i)

/-! ## Deterministic replace-one stability -/

/--
Deterministic **replace-one uniform stability** (a common core notion).

`UniformStableReplace A ℓ β` means that if you replace one example in the training set, then the
loss on *any* test point changes by at most $\beta$.
-/
def UniformStableReplace {n : Nat} (A : LearningMap n Z H) (ℓ : Loss H Z) (β : ℝ) : Prop :=
  ∀ (S : Dataset n Z) (i : Fin n) (z z' : Z),
    |ℓ (A S) z - ℓ (A (replaceAt S i z')) z| ≤ β

/-! ## IID sampling helper -/

section Measure

variable [MeasurableSpace Z]

/--
IID sampling: product distribution on datasets.

If `μ` is a distribution over examples `Z`, then `iid μ n` is the distribution over datasets of size
`n` obtained by sampling each coordinate independently from `μ`.
-/
def iid (μ : MeasureTheory.ProbabilityMeasure Z) (n : Nat) : MeasureTheory.ProbabilityMeasure
  (Dataset n Z) :=
  MeasureTheory.ProbabilityMeasure.pi fun _ : Fin n => μ

end Measure

end LeanSMILES.LearningTheory.Stability
