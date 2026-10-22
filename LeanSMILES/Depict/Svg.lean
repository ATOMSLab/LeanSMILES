/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ejike89
-/
module

public import LeanSMILES.Depict.Layout

/-!
# LeanSMILES.Depict.Svg

The drawing itself, from the coordinates of `LeanSMILES.Depict.Layout`:

* bonds as lines — double and triple bonds as parallel lines, the inner line
  of a ring double bond on the ring side, aromatic bonds with an inner dashed
  line;
* stereo bonds as filled wedges and fanned hashes, narrow end at the centre;
* heteroatoms, charged atoms, isotopes and isolated atoms labelled with their
  symbol, hydrogen count, charge and mass number (`D` and `T` for the heavy
  hydrogens), in CPK-like colours; carbon skeletons unlabelled, as chemists
  draw them.

The picture is built as a small XML tree (`Xml`), so that the same value can
be serialised to an SVG string (`Molecule.svg`) or handed to the editor's
infoview (`LeanSMILES.Depict.Widget`).

`Molecule.molBlock` writes the same drawing as an MDL mol block (V2000) with
the wedge/hash flags, so that any other toolkit can read the depicted
stereochemistry back; `tools/check_depiction.py` does exactly that with RDKit
over `datasets/stereo.smi`.
-/

@[expose] public section

namespace LeanSMILES.Depict

/-- An XML element tree: text, or a tag with attributes and children. -/
inductive Xml where
  /-- Character data. -/
  | text : String → Xml
  /-- An element with its attributes and children. -/
  | elem : String → List (String × String) → List Xml → Xml
  deriving Inhabited, Repr

namespace Xml

/-- Escape `<`, `>`, `&` and `"`. -/
def escape (s : String) : String :=
  s.foldl (fun acc c ↦
    match c with
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '&' => acc ++ "&amp;"
    | '"' => acc ++ "&quot;"
    | c => acc.push c) ""

/-- Serialise. -/
partial def render : Xml → String
  | .text s => escape s
  | .elem tag attrs children =>
    let a := String.join (attrs.map fun (k, v) ↦ s!" {k}=\"{escape v}\"")
    s!"<{tag}{a}>" ++ String.join (children.map render) ++ s!"</{tag}>"

instance : ToString Xml := ⟨render⟩

end Xml

/-- CPK-like colours for atom labels. -/
def color : Option Element → String
  | some .N => "#3050F8"
  | some .O => "#FF0D0D"
  | some .S => "#C8A000"
  | some .P => "#FF8000"
  | some .F => "#20B050"
  | some .Cl => "#1FA01F"
  | some .Br => "#A62929"
  | some .I => "#940094"
  | some .B => "#E07070"
  | some .C => "#222222"
  | some _ => "#8060C0"
  | none => "#666666"

/-- A number with one decimal, for SVG attributes. -/
def num (x : Float) : String := toString ((x * 10).round / 10)

/-- Whether an atom is drawn with a label rather than as a bare vertex: anything
but an uncharged, unlabelled carbon with at least one bond. -/
def labelled (g : Graph) (i : ℕ) : Bool :=
  let a := g.atom i
  a.element != some .C || a.charge != 0 || a.isotope.isSome || g.degree i == 0

/-- The SVG drawing of a depiction graph from given coordinates (bond
lengths, `y` up); `scale` is the bond length in pixels. -/
def svgWith (g : Graph) (pos : Array Pt) (scale : Float := 32) : Xml := Id.run do
  let n := g.numAtoms
  if n == 0 then return .text "(empty molecule)"
  let minX := pos.foldl (fun s p ↦ fmin s p.1) 1e9
  let maxX := pos.foldl (fun s p ↦ fmax s p.1) (-1e9)
  let minY := pos.foldl (fun s p ↦ fmin s p.2) 1e9
  let maxY := pos.foldl (fun s p ↦ fmax s p.2) (-1e9)
  let margin := 22.0
  let W := (maxX - minX) * scale + 2 * margin
  let H := (maxY - minY) * scale + 2 * margin
  -- pixel coordinates, `y` down
  let P (i : ℕ) : Pt :=
    let (x, y) := pos[i]!
    ((x - minX) * scale + margin, (maxY - y) * scale + margin)
  -- the centre of the smallest ring through a ring bond, for the inner line of
  -- a double bond: the shortest path from `u` to `v` avoiding the bond itself
  let ringCenter (u v : ℕ) : Option Pt := Id.run do
    if !g.inRing u v then return none
    let mut prev := Array.replicate n n
    let mut seen := (Array.replicate n false).set! u true
    let mut queue := #[u]
    let mut head := 0
    for _ in [0:n + 1] do
      if h : head < queue.size then
        let x := queue[head]
        head := head + 1
        for (_, y) in g.adj.getD x [] do
          if (x == u && y == v) then continue
          if !seen[y]! then
            seen := seen.set! y true
            prev := prev.set! y x
            queue := queue.push y
      else break
    if !seen[v]! then return none
    let mut ring := [v]
    let mut x := v
    let mut fuel := n
    while x != u && fuel > 0 do
      fuel := fuel - 1
      x := prev[x]!
      ring := x :: ring
    let k := ring.length.toFloat
    return some (ring.foldl (fun s i ↦ s + (P i).1) 0 / k,
      ring.foldl (fun s i ↦ s + (P i).2) 0 / k)
  let line (a b : Pt) (extra : List (String × String) := []) : Xml :=
    .elem "line" ([("x1", num a.1), ("y1", num a.2), ("x2", num b.1), ("y2", num b.2),
      ("stroke", "#222"), ("stroke-width", "1.6"), ("stroke-linecap", "round")] ++ extra) []
  let stereo := wedges g pos
  let mut parts : List Xml := []
  for e in g.edges do
    -- orient stereo bonds from the centre (narrow end) to the neighbor
    let st := stereo.find? fun s ↦
      (s.centre == e.src && s.neighbor == e.dst) || (s.centre == e.dst && s.neighbor == e.src)
    let (u, v) := match st with
      | some s => (s.centre, s.neighbor)
      | none => (e.src, e.dst)
    -- shorten at labelled atoms
    let (x1, y1) := P u
    let (x2, y2) := P v
    let len := fmax (Float.sqrt (sq (x2 - x1) + sq (y2 - y1))) 1e-6
    let (ux, uy) := ((x2 - x1) / len, (y2 - y1) / len)
    let s1 := if labelled g u then 8.0 else 0.0
    let s2 := if labelled g v then 8.0 else 0.0
    let a : Pt := (x1 + ux * s1, y1 + uy * s1)
    let c : Pt := (x2 - ux * s2, y2 - uy * s2)
    let (nx, ny) := (-uy, ux)
    -- a parallel line on the ring side (or the positive normal side), shortened
    let inner (off : Float) (dashed : Bool) : Xml :=
      let side : Float := match ringCenter u v with
        | some (cx, cy) =>
          if (cx - (x1 + x2) / 2) * nx + (cy - (y1 + y2) / 2) * ny > 0 then 1 else -1
        | none => 1
      let sh := 0.18 * len
      line (a.1 + ux * sh + side * nx * off, a.2 + uy * sh + side * ny * off)
           (c.1 - ux * sh + side * nx * off, c.2 - uy * sh + side * ny * off)
           (if dashed then [("stroke-dasharray", "3,3")] else [])
    let parallel (off : Float) : Xml :=
      line (a.1 + nx * off, a.2 + ny * off) (c.1 + nx * off, c.2 + ny * off)
    match e.kind, st with
    | .single, some ⟨_, _, true⟩ =>
      -- wedge: a filled triangle widening towards the neighbor
      parts := parts ++ [.elem "polygon" [("points",
        s!"{num a.1},{num a.2} {num (c.1 + nx * 3.5)},{num (c.2 + ny * 3.5)} \
          {num (c.1 - nx * 3.5)},{num (c.2 - ny * 3.5)}"), ("fill", "#222")] []]
    | .single, some ⟨_, _, false⟩ =>
      -- hash: perpendicular dashes widening towards the neighbor
      parts := parts ++ (List.range 6).map fun t ↦
        let f := (t.toFloat + 1) / 6
        let (px, py) := (a.1 + (c.1 - a.1) * f, a.2 + (c.2 - a.2) * f)
        let w := 3.5 * f
        line (px + nx * w, py + ny * w) (px - nx * w, py - ny * w) [("stroke-width", "1.4")]
    | .single, _ => parts := parts ++ [line a c]
    | .aromatic, _ => parts := parts ++ [line a c, inner 5 true]
    | .double, _ =>
      if (ringCenter u v).isSome then parts := parts ++ [line a c, inner 5 false]
      else parts := parts ++ [parallel 2.5, parallel (-2.5)]
    | .triple, _ => parts := parts ++ [line a c, parallel 4, parallel (-4)]
    | .quadruple, _ =>
      parts := parts ++ [parallel 1.5, parallel (-1.5), parallel 4.5, parallel (-4.5)]
  for i in [0:n] do
    if labelled g i then
      let a := g.atom i
      let (x, y) := P i
      let h := a.totalH
      let hs := if h == 0 then "" else if h == 1 then "H" else "H" ++ toString h
      let chg := if a.charge == 0 then "" else
        (if a.charge.natAbs == 1 then "" else toString a.charge.natAbs) ++
          (if a.charge > 0 then "+" else "−")
      -- isotopes: D and T for the heavy hydrogens, otherwise a mass-number prefix
      let (iso, sym) := match a.element, a.isotope with
        | some .H, some 2 => ("", "D")
        | some .H, some 3 => ("", "T")
        | _, some k => (toString k, a.symbol.capitalize)
        | _, none => ("", a.symbol.capitalize)
      let isoSpan := if iso.isEmpty then [] else
        [Xml.elem "tspan" [("font-size", "9"), ("dy", "-6")] [.text iso],
         Xml.elem "tspan" [("dy", "6")] [.text ""]]
      parts := parts ++ [.elem "text"
        [("x", num x), ("y", num (y + 5)), ("text-anchor", "middle"), ("font-size", "14"),
         ("font-family", "sans-serif"), ("fill", color a.element), ("font-weight", "600")]
        (isoSpan ++ [.text (sym ++ hs),
          .elem "tspan" [("font-size", "10"), ("dy", "-6")] [.text chg]])]
  return .elem "svg" [("width", num W), ("height", num H), ("viewBox", s!"0 0 {num W} {num H}"),
    ("xmlns", "http://www.w3.org/2000/svg")] parts

/-- The SVG drawing of a depiction graph; `scale` is the bond length in pixels. -/
def svgOf (g : Graph) (scale : Float := 32) : Xml := svgWith g (layout g) scale

/-- MDL mol block (V2000) of the drawing from given coordinates, with wedge (`1`)
and hash (`6`) flags
on the stereo bonds and the "either" flag (`3`) on double bonds whose
cis/trans arrangement the SMILES left open. Aromatic atoms that carry
hydrogens get them as explicit atoms, so that readers can kekulize. A
quadruple bond, which V2000 has no code for, is written as `8` (any). -/
def molBlockWith (g : Graph) (pos : Array Pt) : String := Id.run do
  let stereo := wedges g pos
  let coord (x : Float) : String :=
    let s := toString ((x * 10000).round / 10000)
    let s := if s.startsWith "-" then s else " " ++ s
    String.ofList (List.replicate (10 - s.length) ' ') ++ s
  let i3 (k : ℕ) : String :=
    String.ofList (List.replicate (3 - (toString k).length) ' ') ++ toString k
  let hAtoms : Array ℕ := (Array.range g.numAtoms).filter fun i ↦
    (g.atom i).aromatic && (g.atom i).totalH > 0
  let nA := g.numAtoms + hAtoms.size
  let nB := g.edges.size + hAtoms.size
  let mut lines : Array String := #["", "  LeanSMILES", "",
    s!"{i3 nA}{i3 nB}  0  0  0  0  0  0  0  0999 V2000"]
  for i in [0:g.numAtoms] do
    let a := g.atom i
    let (x, y) := pos[i]!
    let symbol := a.symbol.capitalize
    let sym := symbol ++ String.ofList (List.replicate (3 - symbol.length) ' ')
    let chg := match a.charge with
      | 1 => 3 | 2 => 2 | 3 => 1 | -1 => 5 | -2 => 6 | -3 => 7 | _ => 0
    lines := lines.push
      s!"{coord x}{coord y}{coord 0} {sym} 0{i3 chg}  0  0  0  0  0  0  0  0  0  0"
  for i in hAtoms do
    let (x, y) := pos[i]!
    lines := lines.push
      s!"{coord (x + 0.3)}{coord (y + 0.3)}{coord 0} H   0  0  0  0  0  0  0  0  0  0  0  0"
  for e in g.edges do
    let st := stereo.find? fun s ↦
      (s.centre == e.src && s.neighbor == e.dst) || (s.centre == e.dst && s.neighbor == e.src)
    let unspecified := e.kind == .double && !e.ring && !g.stereoSpecified e
    let (u, v, flag) := match st with
      | some s => (s.centre, s.neighbor, if s.wedge then 1 else 6)
      | none => (e.src, e.dst, if unspecified then 3 else 0)
    let o := match e.kind with
      | .single => 1 | .double => 2 | .triple => 3 | .aromatic => 4 | .quadruple => 8
    lines := lines.push s!"{i3 (u + 1)}{i3 (v + 1)}{i3 o}{i3 flag}"
  for hi in [0:hAtoms.size] do
    lines := lines.push s!"{i3 (hAtoms[hi]! + 1)}{i3 (g.numAtoms + hi + 1)}  1  0"
  for i in [0:g.numAtoms] do
    if let some iso := (g.atom i).isotope then
      lines := lines.push s!"M  ISO  1 {i3 (i + 1)} {i3 iso}"
  lines := lines.push "M  END"
  return "\n".intercalate lines.toList ++ "\n"

/-- The mol block of a depiction graph, laid out here. -/
def molBlockOf (g : Graph) : String := molBlockWith g (layout g)

end LeanSMILES.Depict

namespace LeanSMILES

/-- The SVG drawing of a molecule; `scale` is the bond length in pixels. -/
def Molecule.svg {n : ℕ} (m : Molecule n) (scale : Float := 32) : Depict.Xml :=
  Depict.svgOf (Depict.Graph.ofMolecule m) scale

/-- The SVG drawing as a string. -/
def Molecule.svgString {n : ℕ} (m : Molecule n) (scale : Float := 32) : String :=
  (m.svg scale).render

/-- The MDL mol block (V2000) of the drawing, with wedge/hash flags. -/
def Molecule.molBlock {n : ℕ} (m : Molecule n) : String :=
  Depict.molBlockOf (Depict.Graph.ofMolecule m)

/-- The SVG drawing of a parsed molecule. -/
def Mol.svg (M : Mol) (scale : Float := 32) : Depict.Xml := M.mol.svg scale

/-- The SVG drawing as a string. -/
def Mol.svgString (M : Mol) (scale : Float := 32) : String := M.mol.svgString scale

/-- The MDL mol block of the drawing. -/
def Mol.molBlock (M : Mol) : String := M.mol.molBlock

/-- The 2D coordinates of a parsed molecule, in bond lengths with `y` up. -/
def Mol.coordinates (M : Mol) : Array Depict.Pt := Depict.layout (Depict.Graph.ofMol M)

end LeanSMILES
