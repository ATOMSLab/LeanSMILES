import LeanSMILES.Widgets.SVG
import LeanSMILES.API.Stats

/-!
# Charts

Matplotlib-style figures for the infoview, drawn as SVG:

* `histogram` — the distribution plot (`sns.histplot`);
* `scatter` — measured vs. predicted, with the `y = x` "perfect prediction" line;
* `lineChart` — e.g. a training-loss curve.

Display one with `#html`, e.g. `#html histogram values (title := "logS")`.
-/

namespace Widgets

open Lean ProofWidgets

/-- Figure geometry: total size and margins around the plotting area. -/
structure Frame where
  width : Float := 480
  height : Float := 360
  left : Float := 64
  right : Float := 20
  top : Float := 36
  bottom : Float := 52

def Frame.plotW (f : Frame) : Float := f.width - f.left - f.right
def Frame.plotH (f : Frame) : Float := f.height - f.top - f.bottom

/-- About `target` round tick positions covering `[lo, hi]` (steps of 1, 2 or 5 × 10ᵏ). -/
def niceTicks (lo hi : Float) (target : Nat := 6) : Array Float :=
  if hi ≤ lo then #[lo]
  else
    let raw := (hi - lo) / target.toFloat
    let mag := Float.pow 10 (Float.floor (Float.log10 raw))
    let step := [1.0, 2.0, 5.0, 10.0].foldl (fun best k =>
      if (k * mag - raw).abs < (best - raw).abs then k * mag else best) mag
    let first := Float.ceil (lo / step) * step
    let count := (Float.floor ((hi - first) / step)).toUInt64.toNat + 1
    (Array.range count).map fun k => first + k.toFloat * step

/-- A short label for a tick value. -/
def tickLabel (x : Float) : String :=
  if x.abs ≥ 100 || x == x.round then API.formatFloat x 0 else API.formatFloat x 1

/-- Axes, ticks, grid lines, title and axis labels for data ranges `[x0, x1] × [y0, y1]`.
Returns the drawing elements and the data → pixel maps. -/
def axes (f : Frame) (x0 x1 y0 y1 : Float) (title xlabel ylabel : String) :
    Array Html × (Float → Float) × (Float → Float) :=
  let sx := fun x => f.left + (x - x0) / (x1 - x0) * f.plotW
  let sy := fun y => f.top + f.plotH - (y - y0) / (y1 - y0) * f.plotH
  let xt := (niceTicks x0 x1).filter fun t => t ≥ x0 && t ≤ x1
  let yt := (niceTicks y0 y1).filter fun t => t ≥ y0 && t ≤ y1
  let bottomY := f.top + f.plotH
  let elems : Array Html :=
    #[rect 0 0 f.width f.height "white"] ++
    (yt.map fun t => line f.left (sy t) (f.left + f.plotW) (sy t) "#e6e6e6") ++
    (xt.map fun t => line (sx t) f.top (sx t) bottomY "#e6e6e6") ++
    #[rect f.left f.top f.plotW f.plotH "none" [("stroke", toJson "#444")]] ++
    (xt.map fun t => group #[line (sx t) bottomY (sx t) (bottomY + 5) "#444",
      text (sx t) (bottomY + 18) (tickLabel t) 11]) ++
    (yt.map fun t => group #[line (f.left - 5) (sy t) f.left (sy t) "#444",
      text (f.left - 8) (sy t + 4) (tickLabel t) 11 "end"]) ++
    #[text (f.width / 2) 22 title 15 "middle" "#111" [("fontWeight", toJson "bold")],
      text (f.left + f.plotW / 2) (f.height - 12) xlabel 12,
      text 16 (f.top + f.plotH / 2) ylabel 12 "middle" "#222"
        [("transform", toJson s!"rotate(-90 16 {f.top + f.plotH / 2})")]]
  (elems, sx, sy)

def minMax (xs : Array Float) : Float × Float :=
  (xs.foldl min (xs.getD 0 0), xs.foldl max (xs.getD 0 0))

/-- Pad a range by `frac` of its width on both sides (and widen a degenerate range). -/
def pad (lo hi : Float) (frac : Float := 0.05) : Float × Float :=
  if hi ≤ lo then (lo - 1, hi + 1) else (lo - frac * (hi - lo), hi + frac * (hi - lo))

/-- Histogram with `bins` equal-width bins (like `sns.histplot(values, bins=bins)`). -/
def histogram (values : Array Float) (bins : Nat := 30) (title := "Distribution")
    (xlabel := "value") (ylabel := "Frequency") (color := "purple") (f : Frame := {}) :
    Html :=
  let h := API.histogram (Vector.mk values rfl) bins
  let top := h.foldl (fun t (_, _, c) => max t c) 1
  let (lo, hi) := minMax values
  let (els, sx, sy) := axes f lo hi 0 (top.toFloat * 1.08) title xlabel ylabel
  let bars := h.map fun (a, b, c) =>
    rect (sx a) (sy c.toFloat) (max 0 (sx b - sx a - 1)) (sy 0 - sy c.toFloat) color
      [("fillOpacity", toJson 0.75), ("stroke", toJson "white"), ("strokeWidth", toJson 0.5)]
  svg f.width f.height (els ++ bars)

/-- Scatter plot of `(x, y)` pairs. With `identityLine`, draws the dashed green `y = x`
line (the notebook's "perfect prediction" reference). -/
def scatter (points : Array (Float × Float)) (title := "Measured vs Predicted")
    (xlabel := "Measured") (ylabel := "Predicted") (color := "crimson") (alpha := 0.4)
    (identityLine := true) (f : Frame := {}) : Html :=
  let xs := points.map (·.1)
  let ys := points.map (·.2)
  let (xlo, xhi) := minMax xs
  let (ylo, yhi) := minMax ys
  let (lo, hi) := if identityLine then pad (min xlo ylo) (max xhi yhi) else (0, 0)
  let (x0, x1) := if identityLine then (lo, hi) else pad xlo xhi
  let (y0, y1) := if identityLine then (lo, hi) else pad ylo yhi
  let (els, sx, sy) := axes f x0 x1 y0 y1 title xlabel ylabel
  let dots := points.map fun (x, y) =>
    circle (sx x) (sy y) 3.2 color [("fillOpacity", toJson alpha)]
  let ref := if identityLine then
      #[line (sx x0) (sy x0) (sx x1) (sy x1) "green" 1.5 [("strokeDasharray", toJson "6 4")]]
    else #[]
  svg f.width f.height (els ++ dots ++ ref)

/-- One or more line series sharing axes; `series` is `(label, colour, points)`. -/
def lineChart (series : Array (String × String × Array (Float × Float)))
    (title := "") (xlabel := "x") (ylabel := "y") (f : Frame := {}) : Html :=
  let all := series.flatMap (·.2.2)
  let (x0, x1) := pad (minMax (all.map (·.1))).1 (minMax (all.map (·.1))).2 0
  let (y0, y1) := pad (minMax (all.map (·.2))).1 (minMax (all.map (·.2))).2
  let (els, sx, sy) := axes f x0 x1 y0 y1 title xlabel ylabel
  let lines := series.map fun (_, c, pts) => polyline (pts.map fun (x, y) => (sx x, sy y)) c
  let legend := series.mapIdx fun k (name, c, _) =>
    group #[line (f.width - f.right - 120) (f.top + 14 + 16 * k.toFloat)
        (f.width - f.right - 100) (f.top + 14 + 16 * k.toFloat) c 2,
      text (f.width - f.right - 94) (f.top + 18 + 16 * k.toFloat) name 11 "start"]
  svg f.width f.height (els ++ lines ++ legend)

/-- Figures side by side (like `plt.subplots(1, k)`). -/
def row (figures : Array Html) : Html :=
  div figures [("display", toJson "flex"), ("flexWrap", toJson "wrap"), ("gap", toJson "12px")]

end Widgets
