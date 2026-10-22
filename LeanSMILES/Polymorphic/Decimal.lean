module

public import LeanSMILES.Polymorphic.Scalar

/-!
# Decimals

Decimal literals such as `-0.974`, `202.31999999999996` or `1e-5`, read exactly as
`mantissa · 10^exponent`. `Decimal.toScalar` converts to any `Scalar` (exactly over `ℝ`,
`Decimal.toScalar_eq_toReal`); `Decimal.toFloat` (`Float/Scalar.lean`) converts to the
nearest `Float`.
-/

@[expose] public section

namespace Primitives

/-- The exact value `mantissa · 10^exponent`. -/
structure Decimal where
  mantissa : Int
  exponent : Int
  deriving DecidableEq, Repr, Inhabited

def digitsToNat (ds : List Char) : Nat := ds.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- A signed run of digits (the exponent of `1e-5`). -/
def readSignedInt (cs : List Char) : Option (Int × List Char) :=
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty then none
  else some (if neg then -(digitsToNat ds : Int) else digitsToNat ds, cs.drop ds.length)

/-- Parse `[+-]digits[.digits][(e|E)[+-]digits]`, ignoring surrounding whitespace. -/
def Decimal.parse? (s : String) : Option Decimal :=
  let cs := s.trimAscii.toString.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let intDs := cs.takeWhile Char.isDigit
  let cs := cs.drop intDs.length
  let (fracDs, cs) := match cs with
    | '.' :: r => let f := r.takeWhile Char.isDigit; (f, r.drop f.length)
    | r => ([], r)
  let exp? : Option (Int × List Char) := match cs with
    | 'e' :: r | 'E' :: r => readSignedInt r
    | r => some (0, r)
  match exp? with
  | some (e, []) =>
    if intDs.isEmpty && fracDs.isEmpty then none
    else
      let m : Int := digitsToNat (intDs ++ fracDs)
      some ⟨if neg then -m else m, e - fracDs.length⟩
  | _ => none

/-- The value in any `Scalar`: `±|m| · 10^e` or `±|m| / 10^(-e)`. Exact over `ℝ`. -/
def Decimal.toScalar {α : Type} [Scalar α] (d : Decimal) : α :=
  let mag : α :=
    if 0 ≤ d.exponent then Scalar.fromNat (d.mantissa.natAbs * 10 ^ d.exponent.toNat)
    else Scalar.fromNat d.mantissa.natAbs / Scalar.fromNat (10 ^ (-d.exponent).toNat)
  if d.mantissa < 0 then -mag else mag

/-! ## Exact arithmetic -/

instance : OfNat Decimal 0 := ⟨⟨0, 0⟩⟩

/-- Exact sum: both operands are rescaled to the smaller exponent. -/
def Decimal.add (a b : Decimal) : Decimal :=
  let e := min a.exponent b.exponent
  ⟨a.mantissa * 10 ^ (a.exponent - e).toNat + b.mantissa * 10 ^ (b.exponent - e).toNat, e⟩

instance : Add Decimal := ⟨Decimal.add⟩

/-- `k · d`, exactly. -/
def Decimal.nsmul (k : Nat) (d : Decimal) : Decimal := ⟨k * d.mantissa, d.exponent⟩

/-- Decimal notation without exponent, e.g. `457.432` or `-0.77`. -/
def Decimal.toString (d : Decimal) : String :=
  let sign := if d.mantissa < 0 then "-" else ""
  let m := d.mantissa.natAbs
  if 0 ≤ d.exponent then sign ++ s!"{m * 10 ^ d.exponent.toNat}"
  else
    let k := (-d.exponent).toNat
    let digits := s!"{m}"
    let digits := String.ofList (List.replicate (k + 1 - digits.length) '0') ++ digits
    sign ++ digits.take (digits.length - k) ++ "." ++ digits.drop (digits.length - k)

instance : ToString Decimal := ⟨Decimal.toString⟩

end Primitives

end
