import LeanSMILES.API.Split
import LeanSMILES.MetaPrograms.Test

/-! Tests for `trainTestSplit`, `permutation` and `shuffle`. -/

open Primitives ML API

def d : Dataset Float 10 1 :=
  { X := Vector.ofFn fun i => #v[i.val.toFloat], y := Vector.ofFn fun i => i.val.toFloat }

def ids {k : Nat} (s : Dataset Float k 1) : List Nat := s.y.toList.map (·.toUInt64.toNat)

-- sizes follow sklearn: test = ⌈0.2 · m⌉
#test TestSize.testCount (.fraction 1 5) 10 == 2
#test TestSize.testCount (.fraction 1 5) 1115 == 223
#test TestSize.testCount (.fraction 1 3) 10 == 4
#test TestSize.testCount (.count 3) 10 == 3
#test TestSize.testCount (.count 30) 10 == 10

def s := trainTestSplit { testSize := .fraction 3 10, seed := 42 } d
#test (ids s.train).length == 7 && (ids s.test).length == 3
-- train and test partition the rows
#test ((ids s.train) ++ (ids s.test)).mergeSort == List.range 10
-- rows stay intact (X and y move together)
#test (List.finRange 7).all fun i => s.train.X[i][0] == s.train.y[i]
-- the same seed gives the same split; another seed gives a different one
#test ids (trainTestSplit { testSize := .fraction 3 10, seed := 42 } d).test == ids s.test
#test ids (trainTestSplit { testSize := .fraction 3 10, seed := 7 } d).test != ids s.test
-- without shuffling, train is the head and test the tail
#test ids (trainTestSplit { testSize := .count 3, shuffle := false } d).train == List.range 7
#test ids (trainTestSplit { testSize := .count 3, shuffle := false } d).test == [7, 8, 9]

-- permutations contain every index exactly once
#test ((permutation 100 42).toList.map (·.val)).mergeSort == List.range 100
#test (permutation 100 42).toList != (permutation 100 43).toList
#test (shuffle #v['a', 'b', 'c', 'd'] 1).toList.mergeSort (· ≤ ·) == ['a', 'b', 'c', 'd']
#test splitMix64 0 == (16294208416658607535, 11400714819323198485)

-- sizes carried at runtime
def sized := trainTestSplitSized { testSize := .fraction 3 10, seed := 42 } d
#test sized.trainSize == 7 && sized.testSize == 3
#test ids sized.test == ids s.test
