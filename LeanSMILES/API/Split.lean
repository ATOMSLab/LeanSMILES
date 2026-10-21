module

public import LeanSMILES.Machine_Learning.TYPES

/-!
# Train/test split

`trainTestSplit` follows `sklearn.model_selection.train_test_split`:

* `testSize` is a fraction (`.fraction 1 5` = 20 %) or an absolute count;
* the test set has `⌈testSize · m⌉` samples (capped at `m`) and the training set the rest;
* with `shuffle := true`, a seeded permutation is drawn: test = its first `nTest` indices,
  train = the remaining ones (sklearn's `ShuffleSplit` layout). With `shuffle := false`,
  train = the first rows, test = the last rows.

The split sizes are part of the type, so `trainTestSplit` cannot return sets of the wrong
size. The permutation is a Fisher–Yates shuffle driven by SplitMix64 (written with `Nat`
arithmetic). It is deterministic for a given `seed`, but it does not reproduce NumPy's
random stream, so the rows drawn differ from sklearn's for the same `random_state`.
-/

@[expose] public section

namespace API

open Primitives ML

/-! ## Pseudo-random numbers -/

def two64 : Nat := 18446744073709551616

/-- One SplitMix64 step: `(output, next state)`, all values `< 2⁶⁴`. -/
def splitMix64 (s : Nat) : Nat × Nat :=
  let s := (s + 0x9E3779B97F4A7C15) % two64
  let z := ((s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9) % two64
  let z := ((z ^^^ (z >>> 27)) * 0x94D049BB133111EB) % two64
  (z ^^^ (z >>> 31), s)

/-- Fisher–Yates shuffle: for `i = n-1, …, 1`, swap entry `i` with a uniformly drawn
`j ≤ i`. A composition of swaps, so the result is a permutation of `v`. -/
def shuffle {β : Type} {n : Nat} (v : Vector β n) (seed : Nat) : Vector β n :=
  ((List.finRange n).reverse.foldl (fun (v, s) i =>
    let (r, s) := splitMix64 s
    let j : Fin n := ⟨r % (i.val + 1), Nat.lt_of_lt_of_le (Nat.mod_lt _ i.val.succ_pos) i.isLt⟩
    (v.swap i.val j.val i.isLt j.isLt, s)) (v, seed)).1

/-- A seeded random permutation of `0, …, n-1`. -/
def permutation (n seed : Nat) : Vector (Fin n) n := shuffle (Vector.ofFn id) seed

/-! ## Splitting -/

inductive TestSize where
  /-- `num / den` of the samples, rounded up (sklearn's float `test_size`). -/
  | fraction (num den : Nat)
  /-- Exactly this many samples (sklearn's int `test_size`). -/
  | count (k : Nat)
  deriving Repr, DecidableEq

/-- Number of test samples out of `m` (always `≤ m`). -/
def TestSize.testCount (t : TestSize) (m : Nat) : Nat :=
  match t with
  | .fraction num den => min m ((m * num + den - 1) / den)
  | .count k => min m k

theorem TestSize.testCount_le (t : TestSize) (m : Nat) : t.testCount m ≤ m := by
  cases t <;> exact Nat.min_le_left _ _

structure SplitConfig where
  testSize : TestSize := .fraction 1 5
  seed : Nat := 42
  shuffle : Bool := true
  deriving Repr

/-- Training and test sets with `mTrain` and `mTest` samples. -/
structure TrainTestSplit (α : Type) (mTrain mTest n : Nat) where
  train : Dataset α mTrain n
  test : Dataset α mTest n

/-- The rows of `d` at the given indices, in that order. -/
def _root_.ML.Dataset.select {α : Type} {m n k : Nat} (d : Dataset α m n)
    (idx : Vector (Fin m) k) : Dataset α k n :=
  { X := idx.map fun i => d.X[i], y := idx.map fun i => d.y[i] }

/-- The `(train indices, test indices)` of a split of `m` samples. -/
def splitIndices (cfg : SplitConfig) (m : Nat) :
    Vector (Fin m) (m - cfg.testSize.testCount m) × Vector (Fin m) (cfg.testSize.testCount m) :=
  let k := cfg.testSize.testCount m
  have hk : k ≤ m := cfg.testSize.testCount_le m
  if cfg.shuffle then
    let p := permutation m cfg.seed
    (Vector.ofFn fun j => p[k + j.val]'(by omega), Vector.ofFn fun j => p[j.val]'(by omega))
  else
    (Vector.ofFn fun j => ⟨j.val, by omega⟩, Vector.ofFn fun j => ⟨m - k + j.val, by omega⟩)

/-- Split a dataset into training and test sets (see the module docstring). -/
def trainTestSplit {α : Type} {m n : Nat} (cfg : SplitConfig) (d : Dataset α m n) :
    TrainTestSplit α (m - cfg.testSize.testCount m) (cfg.testSize.testCount m) n :=
  let (trainIdx, testIdx) := splitIndices cfg m
  { train := d.select trainIdx, test := d.select testIdx }

/-- A split whose sizes are carried as fields. In a notebook the sizes are only known
once the data is loaded, so this avoids writing them in types. -/
structure SizedSplit (α : Type) (n : Nat) where
  trainSize : Nat
  testSize : Nat
  train : Dataset α trainSize n
  test : Dataset α testSize n

/-- `trainTestSplit` with the sizes packed into the result. -/
def trainTestSplitSized {α : Type} {m n : Nat} (cfg : SplitConfig) (d : Dataset α m n) :
    SizedSplit α n :=
  let s := trainTestSplit cfg d
  { trainSize := _, testSize := _, train := s.train, test := s.test }

end API

end
