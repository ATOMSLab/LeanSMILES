import LeanSMILES.Widgets.SVG

/-!
# Tables

An HTML table in the style of a pandas `DataFrame` display (`df.head(10)`).
-/

namespace Widgets

open Lean ProofWidgets

def cellStyle (header : Bool) (alt : Bool) : Json :=
  Json.mkObj ([("padding", toJson "4px 10px"), ("borderBottom", toJson "1px solid #ddd"),
    ("textAlign", toJson (if header then "left" else "right")),
    ("fontFamily", toJson "DejaVu Sans, Arial, sans-serif"), ("fontSize", toJson "12px"),
    ("color", toJson "#222")] ++
    (if header then [("fontWeight", toJson "bold"), ("background", toJson "#f0f0f0")]
     else [("background", toJson (if alt then "#fafafa" else "white"))]))

/-- A table with a header row; the first column is the index, like pandas. -/
def table (header : Array String) (rows : Array (Array String)) (caption : String := "") :
    Html :=
  let th := fun (s : String) => Html.element "th" #[("style", cellStyle true false)] #[.text s]
  let td := fun (alt : Bool) (s : String) =>
    Html.element "td" #[("style", cellStyle false alt)] #[.text s]
  let body := rows.mapIdx fun k r => Html.element "tr" #[] (r.map (td (k % 2 == 1)))
  let cap := if caption.isEmpty then #[] else
    #[Html.element "caption" #[("style", Json.mkObj [("textAlign", toJson "left"),
      ("fontWeight", toJson "bold"), ("padding", toJson "4px 0"), ("color", toJson "#222")])]
      #[.text caption]]
  Html.element "table" #[("style", Json.mkObj [("borderCollapse", toJson "collapse"),
      ("background", toJson "white")])]
    (cap ++ #[Html.element "thead" #[] #[Html.element "tr" #[] (header.map th)],
      Html.element "tbody" #[] body])

/-- A two-column `name | value` table. -/
def keyValueTable (rows : Array (String × String)) (caption : String := "") : Html :=
  table #["", "value"] (rows.map fun (k, v) => #[k, v]) caption

end Widgets
