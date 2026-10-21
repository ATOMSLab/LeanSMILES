import LeanSMILES.API.CSV
import LeanSMILES.MetaPrograms.Test

/-! Tests for `Decimal.parse?`, `Decimal.toFloat` and `Decimal.toScalar`. -/

open Primitives API

#test Decimal.parse? "-0.9740000000000001" == some ⟨-9740000000000001, -16⟩
#test Decimal.parse? "202.31999999999996" == some ⟨20231999999999996, -14⟩
#test Decimal.parse? "42" == some ⟨42, 0⟩
#test Decimal.parse? " +3.5 " == some ⟨35, -1⟩
#test Decimal.parse? "1e-5" == some ⟨1, -5⟩
#test Decimal.parse? "2.5E3" == some ⟨25, 2⟩
#test Decimal.parse? ".5" == some ⟨5, -1⟩
#test ["", "-", "abc", "1.2.3", "1e", "1e+", "--1", "1 2"].all (Decimal.parse? · == none)

#test (Decimal.parse? "-0.77").map Decimal.toFloat == some (-0.77)
#test (Decimal.parse? "457.4320000000001").map Decimal.toFloat == some 457.4320000000001
#test (Decimal.parse? "2.5E3").map Decimal.toFloat == some 2500.0
-- the generic conversion agrees with `toFloat` to within an ulp or so
#test ["-0.77", "457.4320000000001", "1e-5", "-11.6"].all fun s =>
  match Decimal.parse? s with
  | some d => (d.toScalar (α := Float) - d.toFloat).abs ≤ 1e-15 * d.toFloat.abs
  | none => false

-- exact arithmetic
#test (Decimal.mk 12011 (-3) + Decimal.mk 4032 (-3)).toString == "16.043"
#test (Decimal.mk 15 (-1) + Decimal.mk 2 0).toString == "3.5"
#test (Decimal.nsmul 4 ⟨1008, -3⟩).toString == "4.032"
#test (Decimal.mk (-77) (-2)).toString == "-0.77"
#test (Decimal.mk 5 (-3)).toString == "0.005"
#test (Decimal.mk 42 2).toString == "4200"
