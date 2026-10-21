module

public import LeanSMILES.Primitives.lin_algebra

/-!
# Descriptive statistics

`describe` (like `pandas.Series.describe`) and `histogram`, a text replacement for the
notebook's distribution plot.
-/

@[expose] public section

namespace API

open Primitives

variable {α : Type} [Scalar α] {m : Nat}

/-- `x` with `decimals` digits after the point (rounded half away from zero). -/
def formatFloat (x : Float) (decimals : Nat := 2) : String :=
  let n := (x.abs * (10 : Float) ^ decimals.toFloat).round.toUInt64.toNat
  let frac := toString (n % 10 ^ decimals)
  let sign := if x < 0 && n != 0 then "-" else ""
  let pad := String.ofList (List.replicate (decimals - frac.length) '0')
  sign ++ toString (n / 10 ^ decimals) ++ (if decimals = 0 then "" else "." ++ pad ++ frac)

structure Summary (α : Type) where
  count : Nat
  mean : α
  /-- Sample standard deviation (`ddof = 1`, as in pandas). -/
  std : α
  min : α
  max : α

def describe (v : Vec α m) : Summary α :=
  let μ := vsum v / Scalar.fromNat m
  let ss := sumFin fun (i : Fin m) => (v[i] - μ) * (v[i] - μ)
  { count := m, mean := μ, std := Scalar.sqrt (ss / Scalar.fromNat (m - 1))
    min := v.toList.foldl Scalar.min (v.toList.headD 0)
    max := v.toList.foldl Scalar.max (v.toList.headD 0) }

/-- Counts in `bins` equal-width bins between the minimum and the maximum; the maximum
falls in the last bin. -/
def histogram (v : Vector Float m) (bins : Nat) : Array (Float × Float × Nat) :=
  let s := describe v
  let width := (s.max - s.min) / bins.toFloat
  let binOf := fun (x : Float) =>
    if width ≤ 0 then 0 else min (bins - 1) ((x - s.min) / width).floor.toUInt64.toNat
  let counts := v.toList.foldl (fun c x => c.modify (binOf x) (· + 1)) (Array.replicate bins 0)
  counts.mapIdx fun b c => (s.min + b.toFloat * width, s.min + (b + 1).toFloat * width, c)

/-- The histogram as text bars, scaled so the largest bin is `barWidth` characters. -/
def histogramText (v : Vector Float m) (bins : Nat) (barWidth : Nat := 50) : String :=
  let h := histogram v bins
  let top := h.foldl (fun t (_, _, c) => max t c) 1
  String.intercalate "\n" (h.toList.map fun (lo, hi, c) =>
    let bar := String.ofList (List.replicate (c * barWidth / top) '#')
    s!"[{formatFloat lo}, {formatFloat hi}) {bar} {c}")

end API

end
