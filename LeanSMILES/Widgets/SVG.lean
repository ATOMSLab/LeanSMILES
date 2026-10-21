import ProofWidgets.Component.HtmlDisplay

/-!
# SVG helpers

Small constructors for `ProofWidgets.Html` SVG elements, used by the chart and molecule
widgets. Attribute names are React's (camelCase), because the infoview renders `Html`
with React.
-/

namespace Widgets

open Lean ProofWidgets

/-- An element with attributes and children. -/
def el (tag : String) (attrs : List (String × Json)) (children : Array Html := #[]) : Html :=
  .element tag attrs.toArray children

def svg (width height : Float) (children : Array Html) : Html :=
  el "svg" [("width", toJson width), ("height", toJson height),
    ("viewBox", toJson s!"0 0 {width} {height}"), ("xmlns", toJson "http://www.w3.org/2000/svg")]
    children

def rect (x y w h : Float) (fill : String) (extra : List (String × Json) := []) : Html :=
  el "rect" ([("x", toJson x), ("y", toJson y), ("width", toJson w), ("height", toJson h),
    ("fill", toJson fill)] ++ extra)

def line (x1 y1 x2 y2 : Float) (stroke : String) (width : Float := 1)
    (extra : List (String × Json) := []) : Html :=
  el "line" ([("x1", toJson x1), ("y1", toJson y1), ("x2", toJson x2), ("y2", toJson y2),
    ("stroke", toJson stroke), ("strokeWidth", toJson width)] ++ extra)

def circle (cx cy r : Float) (fill : String) (extra : List (String × Json) := []) : Html :=
  el "circle" ([("cx", toJson cx), ("cy", toJson cy), ("r", toJson r),
    ("fill", toJson fill)] ++ extra)

def polyline (points : Array (Float × Float)) (stroke : String) (width : Float := 1.5) : Html :=
  el "polyline" [("points", toJson (" ".intercalate (points.toList.map fun (x, y) => s!"{x},{y}"))),
    ("fill", toJson "none"), ("stroke", toJson stroke), ("strokeWidth", toJson width)]

/-- Text; `anchor` is `start`, `middle` or `end`. -/
def text (x y : Float) (s : String) (size : Float := 12) (anchor := "middle")
    (fill := "#222") (extra : List (String × Json) := []) : Html :=
  el "text" ([("x", toJson x), ("y", toJson y), ("fontSize", toJson size),
    ("textAnchor", toJson anchor), ("fill", toJson fill),
    ("fontFamily", toJson "DejaVu Sans, Arial, sans-serif")] ++ extra) #[.text s]

def group (children : Array Html) (extra : List (String × Json) := []) : Html :=
  el "g" extra children

/-- A plain HTML container (for layouts of several figures). -/
def div (children : Array Html) (style : List (String × Json) := []) : Html :=
  el "div" [("style", Json.mkObj style)] children

/-! ## Export (like `plt.savefig`) -/

/-- React attribute name → SVG attribute name (`strokeWidth` → `stroke-width`). -/
def svgAttrName (name : String) : String :=
  if name == "viewBox" then name
  else String.join (name.toList.map fun c => if c.isUpper then s!"-{c.toLower}" else c.toString)

def escapeXml (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

def jsonAttrValue : Json → String
  | .str s => s
  | j => j.compress

/-- Serialize an `Html` tree of SVG/HTML elements as markup (components are dropped). -/
partial def toMarkup : Html → String
  | .element tag attrs children =>
    let attrs := attrs.toList.filterMap fun (k, v) =>
      if k == "style" then none else some s!" {svgAttrName k}=\"{escapeXml (jsonAttrValue v)}\""
    s!"<{tag}{String.join attrs}>{String.join (children.toList.map toMarkup)}</{tag}>"
  | .text s => escapeXml s
  | .component .. => ""

/-- Write a figure to an `.svg` file. -/
def saveSVG (path : System.FilePath) (h : Html) : IO Unit := IO.FS.writeFile path (toMarkup h)

end Widgets
