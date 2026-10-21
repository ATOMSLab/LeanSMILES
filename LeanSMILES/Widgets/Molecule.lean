import LeanSMILES.Widgets.SVG
import LeanSMILES.SMILES.EXECUTABLES

/-!
# Molecule drawings

RDKit-style 2D depictions (`Draw.MolToImage`, `Draw.MolsToGridImage`). Coordinates come
from `Chem.Exec.layout2D` (stress majorization over graph distances). Bonds are drawn
as lines: double bonds with a second line on the inside of rings, aromatic bonds with a
dashed inner line, and triple bonds with three lines. Heteroatoms are labelled in CPK
colours, with their hydrogens and charges.
-/

namespace Widgets

open Lean ProofWidgets Chem

/-- CPK-style label colours. -/
def atomColor : Nat → String
  | 7 => "#2F4FD8"
  | 8 => "#E01010"
  | 9 | 17 => "#1C9A1C"
  | 15 => "#E07000"
  | 16 => "#B89400"
  | 35 => "#A02828"
  | 53 => "#8A008A"
  | 5 => "#C06060"
  | _ => "#222222"

def subscript (k : Nat) : String :=
  String.ofList ((toString k).toList.map fun c =>
    Char.ofNat (0x2080 + (c.toNat - '0'.toNat)))

def chargeLabel (q : Int) : String :=
  if q = 0 then "" else
    let sign := if q > 0 then "⁺" else "⁻"
    let k := q.natAbs
    if k = 1 then sign else
      String.ofList ((toString k).toList.map fun c =>
        match c with
        | '1' => '¹' | '2' => '²' | '3' => '³'
        | d => Char.ofNat (0x2070 + (d.toNat - '0'.toNat))) ++ sign

/-- The label of atom `i`, or `none` for an unlabelled carbon. -/
def atomLabel (m : Molecule) (i : Nat) : Option String :=
  let a := m.atom i
  if a.element == 6 && a.charge == 0 && a.isotope.isNone && m.degree i > 0 then none
  else
    let h := m.totalH i
    let hs := if h = 0 then "" else if h = 1 then "H" else "H" ++ subscript h
    let iso := match a.isotope with | some k => s!"{k}" | none => ""
    some s!"{iso}{symbolOf a.element}{hs}{chargeLabel a.charge}"

/-- An SVG drawing of `m`, `size` pixels square, with an optional caption. -/
def moleculeSvg (m : Molecule) (size : Float := 280) (legend : String := "") : Html :=
  let n := m.atoms.size
  let pos := Chem.Exec.layout2D m
  let xs := pos.map (·.1)
  let ys := pos.map (·.2)
  let (x0, x1) := (xs.foldl min (xs.getD 0 0), xs.foldl max (xs.getD 0 0))
  let (y0, y1) := (ys.foldl min (ys.getD 0 0), ys.foldl max (ys.getD 0 0))
  let padding := 28.0
  let captionH := if legend.isEmpty then 0 else 22
  let avail := size - 2 * padding
  let scale := min 42 (avail / max 1e-9 (max (x1 - x0) (y1 - y0)))
  let offX := padding + (avail - (x1 - x0) * scale) / 2
  let offY := padding + (avail - captionH - (y1 - y0) * scale) / 2
  let px := fun (i : Nat) => let (x, y) := pos.getD i (0, 0); (offX + (x - x0) * scale, offY + (y - y0) * scale)
  let labels := (Array.range n).map (atomLabel m)
  -- shrink a bond end that meets a label
  let trimEnd := fun (i : Nat) (fromX fromY toX toY : Float) =>
    if (labels.getD i none).isSome then
      let dx := toX - fromX; let dy := toY - fromY
      let len := Float.sqrt (dx * dx + dy * dy)
      let t := if len ≤ 0 then 0 else min 0.45 (9 / len)
      (fromX + t * dx, fromY + t * dy)
    else (fromX, fromY)
  let bondEls := m.bonds.toList.flatMap fun b =>
    let (ax, ay) := px b.src
    let (bx, by_) := px b.dst
    let (ax', ay') := trimEnd b.src ax ay bx by_
    let (bx', by') := trimEnd b.dst bx by_ ax ay
    let dx := bx - ax; let dy := by_ - ay
    let len := max 1e-9 (Float.sqrt (dx * dx + dy * dy))
    let (nx, ny) := (-dy / len, dx / len)
    -- which side is "inside": towards the centroid of the other neighbours
    let others := ((m.neighbors b.src).map (·.1) ++ (m.neighbors b.dst).map (·.1)).filter
      fun u => u != b.src && u != b.dst
    let (cx, cy) := if others.isEmpty then (ax, ay) else
      let pts := others.map px
      (pts.foldl (fun s p => s + p.1) 0 / others.length.toFloat,
        pts.foldl (fun s p => s + p.2) 0 / others.length.toFloat)
    let side := if ((cx - ax) * nx + (cy - ay) * ny) ≥ 0 then 1.0 else -1.0
    let main := line ax' ay' bx' by' "#222" 1.6
    let inner (dashed : Bool) :=
      let o := 5.0 * side
      let sh := 0.14
      line (ax' + sh * (bx' - ax') + o * nx) (ay' + sh * (by' - ay') + o * ny)
        (bx' - sh * (bx' - ax') + o * nx) (by' - sh * (by' - ay') + o * ny) "#222" 1.4
        (if dashed then [("strokeDasharray", toJson "3 3")] else [])
    match b.order with
    | .single => [main]
    | .double =>
      if others.isEmpty then
        [line (ax' + 2.5 * nx) (ay' + 2.5 * ny) (bx' + 2.5 * nx) (by' + 2.5 * ny) "#222" 1.5,
         line (ax' - 2.5 * nx) (ay' - 2.5 * ny) (bx' - 2.5 * nx) (by' - 2.5 * ny) "#222" 1.5]
      else [main, inner false]
    | .triple =>
      [main, line (ax' + 4 * nx) (ay' + 4 * ny) (bx' + 4 * nx) (by' + 4 * ny) "#222" 1.3,
       line (ax' - 4 * nx) (ay' - 4 * ny) (bx' - 4 * nx) (by' - 4 * ny) "#222" 1.3]
    | .aromatic => [main, inner true]
  let atomEls := (List.range n).filterMap fun i =>
    (labels.getD i none).map fun lab =>
      let (x, y) := px i
      text x (y + 5) lab 14 "middle" (atomColor (m.atom i).element)
        [("fontWeight", toJson "bold")]
  let caption := if legend.isEmpty then #[] else #[text (size / 2) (size - 8) legend 11]
  svg size size (#[rect 0 0 size size "white"] ++ bondEls.toArray ++ atomEls.toArray ++ caption)

/-- Draw a SMILES string, or show the parse error. -/
def smilesSvg (s : String) (size : Float := 280) (legend : Option String := none) : Html :=
  match Chem.Exec.molFromSmiles s with
  | .ok m => moleculeSvg m size (legend.getD s)
  | .error e =>
    svg size 60 #[rect 0 0 size 60 "#fff4f4", text (size / 2) 34 s!"invalid SMILES: {e}" 12]

/-- A grid of drawings (RDKit's `MolsToGridImage`): `(SMILES, caption)` pairs. -/
def moleculeGrid (mols : Array (String × String)) (perRow : Nat := 4) (cell : Float := 200) :
    Html :=
  let rows := (mols.size + perRow - 1) / perRow
  let cells := mols.mapIdx fun k (s, cap) =>
    let x := (k % perRow).toFloat * cell
    let y := (k / perRow).toFloat * cell
    group #[smilesSvg s cell (some cap)] [("transform", toJson s!"translate({x} {y})")]
  svg (perRow.toFloat * cell) (rows.toFloat * cell)
    (#[rect 0 0 (perRow.toFloat * cell) (rows.toFloat * cell) "white"] ++ cells)

end Widgets
