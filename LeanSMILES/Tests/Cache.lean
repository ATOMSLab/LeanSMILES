import LeanSMILES.MetaPrograms.Cache
import LeanSMILES.MetaPrograms.Test

/-! Tests for `cached def`: the value is computed once and read back from the cache. -/

cached def squares : Array Nat := (Array.range 10).map (· ^ 2)

#eval squares
#test squares.size == 10
#test squares[9]! == 81
-- logically it is still the definition
example : squares = (Array.range 10).map (· ^ 2) := by unfold squares; rfl
