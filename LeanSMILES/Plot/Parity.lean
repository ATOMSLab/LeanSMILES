/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/

/-!
# Parity plots as SVG

A parity plot puts each molecule at (measured, predicted): a perfect model puts
every point on the diagonal. `paritySvg` writes one as a self-contained SVG
document — square axes on a shared scale with integer ticks, the diagonal, a
band of ±1 unit around it, training points hollow, test points filled, and a
legend with each set's size, R² and RMSE.
-/

namespace LeanSMILES.Plot

/-- `x` with `d` decimals, `minus` as the minus sign ("-" for coordinates,
"−" for labels). -/
def fixed (x : Float) (d : Nat := 1) (minus : String := "-") : String :=
  let scale := (10 : Float) ^ d.toFloat
  let n := (x.abs * scale).round.toUInt64.toNat
  let sign := if x < 0 && n != 0 then minus else ""
  let whole := toString (n / 10 ^ d)
  if d == 0 then sign ++ whole
  else
    let frac := toString (n % 10 ^ d)
    sign ++ whole ++ "." ++ String.ofList (List.replicate (d - frac.length) '0') ++ frac

/-- One set of points with its legend entry. -/
structure Series where
  label : String
  /-- (measured, predicted) pairs. -/
  points : Array (Float × Float)
  r2 : Float
  rmse : Float
  /-- Filled points (test) or hollow (training). -/
  filled : Bool

/-- A parity plot of the series, as an SVG document. `axis` names the quantity
with its unit, e.g. "log solubility (log mol/L)". -/
def paritySvg (title subtitle axis : String) (series : List Series) : String := Id.run do
  let all := series.flatMap fun s ↦ s.points.toList.flatMap fun (y, p) ↦ [y, p]
  let lo := (all.foldl min 0).floor
  let hi := (all.foldl max 0).ceil
  let span := hi - lo
  let stepT : Float := if span > 8 then 2 else 1
  -- width, height, left/right/top margins; the bottom margin is what remains
  let (W, H, L, R, T) := ((600 : Float), (660 : Float), (78 : Float), (26 : Float), (92 : Float))
  let size := W - L - R
  let sx (v : Float) := L + (v - lo) / span * size
  let sy (v : Float) := T + size - (v - lo) / span * size
  let c (v : Float) := fixed v 1
  let mut out := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {c W} {c H}\" \
    width=\"{c W}\" height=\"{c H}\" font-family=\"Helvetica, Arial, sans-serif\">\n"
  out := out ++ s!"<rect width=\"{c W}\" height=\"{c H}\" fill=\"#ffffff\"/>\n"
  out := out ++ s!"<text x=\"{c L}\" y=\"34\" font-size=\"19\" font-weight=\"700\" \
    fill=\"#172026\">{title}</text>\n"
  out := out ++ s!"<text x=\"{c L}\" y=\"56\" font-size=\"13\" fill=\"#5b6a73\">{subtitle}</text>\n"
  -- grid and ticks
  let nTicks := (span / stepT).toUInt64.toNat
  for k in [0:nTicks + 1] do
    let v := lo + stepT * k.toFloat
    out := out ++ s!"<line x1=\"{c (sx v)}\" y1=\"{c T}\" x2=\"{c (sx v)}\" y2=\"{c (T + size)}\" \
      stroke=\"#e3e9ec\"/>\n"
    out := out ++ s!"<line x1=\"{c L}\" y1=\"{c (sy v)}\" x2=\"{c (L + size)}\" y2=\"{c (sy v)}\" \
      stroke=\"#e3e9ec\"/>\n"
    out := out ++ s!"<text x=\"{c (sx v)}\" y=\"{c (T + size + 20)}\" font-size=\"12\" \
      text-anchor=\"middle\" fill=\"#5b6a73\">{fixed v 0 "−"}</text>\n"
    out := out ++ s!"<text x=\"{c (L - 10)}\" y=\"{c (sy v + 4)}\" font-size=\"12\" \
      text-anchor=\"end\" fill=\"#5b6a73\">{fixed v 0 "−"}</text>\n"
  -- ±1 band and the diagonal
  out := out ++ s!"<polygon points=\"{c (sx lo)},{c (sy (lo + 1))} {c (sx (hi - 1))},{c (sy hi)} \
    {c (sx hi)},{c (sy hi)} {c (sx hi)},{c (sy (hi - 1))} {c (sx (lo + 1))},{c (sy lo)} \
    {c (sx lo)},{c (sy lo)}\" fill=\"#3b3fa6\" fill-opacity=\"0.07\"/>\n"
  out := out ++ s!"<line x1=\"{c (sx lo)}\" y1=\"{c (sy lo)}\" x2=\"{c (sx hi)}\" y2=\"{c (sy hi)}\" \
    stroke=\"#3b3fa6\" stroke-width=\"1.2\" stroke-dasharray=\"5 4\"/>\n"
  out := out ++ s!"<rect x=\"{c L}\" y=\"{c T}\" width=\"{c size}\" height=\"{c size}\" fill=\"none\" \
    stroke=\"#9fb0b9\"/>\n"
  -- points: hollow series first, filled on top
  for s in series.filter (!·.filled) ++ series.filter (·.filled) do
    for (y, p) in s.points do
      out := out ++ (if s.filled then
        s!"<circle cx=\"{c (sx y)}\" cy=\"{c (sy p)}\" r=\"3.3\" fill=\"#d0641c\" \
          fill-opacity=\"0.85\" stroke=\"#ffffff\" stroke-width=\"0.6\"/>\n"
      else
        s!"<circle cx=\"{c (sx y)}\" cy=\"{c (sy p)}\" r=\"2.8\" fill=\"none\" stroke=\"#7d93a3\" \
          stroke-opacity=\"0.75\" stroke-width=\"1\"/>\n")
  -- legend
  let mut ly := T + 22
  for s in series do
    let mark := if s.filled then
        s!"<circle cx=\"{c (L + 18)}\" cy=\"{c (ly - 4)}\" r=\"4\" fill=\"#d0641c\"/>"
      else s!"<circle cx=\"{c (L + 18)}\" cy=\"{c (ly - 4)}\" r=\"3.6\" fill=\"none\" \
        stroke=\"#7d93a3\" stroke-width=\"1.2\"/>"
    out := out ++ mark ++ s!"<text x=\"{c (L + 30)}\" y=\"{c ly}\" font-size=\"13\" fill=\"#172026\">\
      {s.label} (n = {s.points.size}) · R² {fixed s.r2 3 "−"} · RMSE {fixed s.rmse 2 "−"}</text>\n"
    ly := ly + 20
  out := out ++ s!"<text x=\"{c (L + 18)}\" y=\"{c ly}\" font-size=\"12\" fill=\"#5b6a73\">\
    shaded: within ±1 of the diagonal</text>\n"
  -- axis titles
  out := out ++ s!"<text x=\"{c (L + size / 2)}\" y=\"{c (H - 18)}\" font-size=\"14\" \
    text-anchor=\"middle\" fill=\"#172026\">Measured {axis}</text>\n"
  out := out ++ s!"<text transform=\"translate(22 {c (T + size / 2)}) rotate(-90)\" font-size=\"14\" \
    text-anchor=\"middle\" fill=\"#172026\">Predicted {axis}</text>\n"
  return out ++ "</svg>\n"

end LeanSMILES.Plot
