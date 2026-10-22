/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Depict.Svg
public import LeanSMILES.Fingerprint.Morgan
public import LeanSMILES.Aromaticity.Perceive

/-!
# LeanSMILES.Depict.Fingerprint

A Morgan fingerprint drawn two ways, as an SVG `Xml` tree like the molecule
drawings of `LeanSMILES.Depict.Svg`:

* **grid**, QR-code style: the `fpSize` bits row by row, 64 to a row (2048 bits
  make 32 rows), bit 0 top left; a filled cell is a bit that is on;
* **barcode**: the same bits in one line, bit 0 on the left, one bar per bit
  that is on.

Given a second fingerprint, the bits both have are drawn in a second colour and
the header gives their number and the Tanimoto similarity.

A bit's position is a hash of an atom environment folded modulo `fpSize`, so
neighbouring cells are unrelated; the picture shows how many bits are on and
which ones two molecules share, not where anything sits in the molecule.

```lean
#fingerprint "COc1cc2ncnc(Nc3ccc(F)c(Cl)c3)c2cc1OCCCN1CCOCC1"   -- gefitinib
#fingerprint "CC(=O)Oc1ccccc1C(=O)O", "COc1cc2ncnc(Nc3ccc(F)c(Cl)c3)c2cc1OCCCN1CCOCC1"
```

`#fingerprint` (`LeanSMILES.Depict.Widget`) parses with
`SMILES.parseAromatized`, so the bits are RDKit's; `lake exe depict
--fingerprint` writes the same SVG to a file.
-/

@[expose] public section

namespace LeanSMILES.Depict

/-- Bits that are on. -/
def fpInk : String := "#1f2328"
/-- Bits that are on in both fingerprints. -/
def fpShared : String := "#d85a30"
/-- Grid lines and the frame. -/
def fpGrid : String := "#e3e6ea"
/-- Secondary text. -/
def fpMuted : String := "#5b6a73"

/-- A filled rectangle. -/
def rectXml (x y w h : Float) (fill : String) : Xml :=
  .elem "rect" [("x", num x), ("y", num y), ("width", num w), ("height", num h),
    ("fill", fill)] []

/-- A line of text, `x` and `y` at its baseline start. -/
def textXml (x y : Float) (size : ℕ) (fill s : String) : Xml :=
  .elem "text" [("x", num x), ("y", num y), ("font-size", toString size), ("fill", fill),
    ("font-family", "Helvetica, Arial, sans-serif")] [.text s]

/-- A line from `(x₁, y₁)` to `(x₂, y₂)`. -/
def lineXml (x₁ y₁ x₂ y₂ : Float) (stroke : String) : Xml :=
  .elem "line" [("x1", num x₁), ("y1", num y₁), ("x2", num x₂), ("y2", num y₂),
    ("stroke", stroke), ("stroke-width", "0.5")] []

/-- The colour of an on bit: `fpShared` if `shared` has it too. -/
def bitColor (shared : List ℕ) (b : ℕ) : String := if shared.contains b then fpShared else fpInk

/-- The bits as a grid of `cols` columns, top left corner at `(x, y)`, cells
`cell` pixels wide. -/
def fingerprintGrid (bits : List ℕ) (shared : List ℕ := []) (fpSize : ℕ := 2048)
    (cols : ℕ := 64) (cell : Float := 8) (x y : Float := 0) : List Xml :=
  let rows := (fpSize + cols - 1) / cols
  let W := cols.toFloat * cell
  let H := rows.toFloat * cell
  let vertical := (List.range (cols + 1)).map fun i ↦
    lineXml (x + i.toFloat * cell) y (x + i.toFloat * cell) (y + H) fpGrid
  let horizontal := (List.range (rows + 1)).map fun j ↦
    lineXml x (y + j.toFloat * cell) (x + W) (y + j.toFloat * cell) fpGrid
  let cells := (bits.filter (· < fpSize)).map fun b ↦
    rectXml (x + (b % cols).toFloat * cell) (y + (b / cols).toFloat * cell) cell cell
      (bitColor shared b)
  rectXml x y W H "#ffffff" :: vertical ++ horizontal ++ cells

/-- The bits as a barcode `width` × `height` pixels, top left corner at `(x, y)`.
Bars are at least 1.5 pixels wide so that single bits stay visible. -/
def fingerprintBarcode (bits : List ℕ) (shared : List ℕ := []) (fpSize : ℕ := 2048)
    (width : Float := 512) (height : Float := 56) (x y : Float := 0) : List Xml :=
  let step := width / fpSize.toFloat
  let bw := if step < 1.5 then 1.5 else step
  let frame := Xml.elem "rect" [("x", num x), ("y", num y), ("width", num width),
    ("height", num height), ("fill", "#ffffff"), ("stroke", fpGrid)] []
  frame :: (bits.filter (· < fpSize)).map fun b ↦
    rectXml (x + b.toFloat * step) y bw height (bitColor shared b)

/-- `a / b` with two decimals, for `0 ≤ a ≤ b`. -/
def ratio2 (a b : ℕ) : String :=
  if b == 0 then "0.00" else
  let r := (200 * a + b) / (2 * b)
  s!"{r / 100}.{if r % 100 < 10 then "0" else ""}{r % 100}"

/-- The whole picture: a header (`label`, bits on, and against `other` the shared
bits and Tanimoto similarity), the grid, the barcode and a legend. `other` is
the second fingerprint's bits and name. -/
def fingerprintSvg (bits : List ℕ) (label : String := "")
    (other : Option (List ℕ × String) := none) (fpSize : ℕ := 2048) (cols : ℕ := 64) :
    Xml := Id.run do
  let cell : Float := 8
  let margin : Float := 16
  let W := cols.toFloat * cell
  let rows := (fpSize + cols - 1) / cols
  let shared := match other with
    | some (o, _) => bits.filter o.contains
    | none => []
  let mut parts : List Xml := []
  let mut y := margin + 14
  if !label.isEmpty then
    parts := parts ++ [textXml margin y 14 fpInk label]
    y := y + 20
  let on := s!"{bits.length} of {fpSize} bits on"
  match other with
  | some (o, name) =>
    let union := bits.length + o.length - shared.length
    parts := parts ++ [textXml margin y 12 fpMuted
        s!"{on} · {shared.length} shared · Tanimoto {ratio2 shared.length union}",
      textXml margin (y + 18) 12 fpMuted s!"compared with {name}"]
    y := y + 18 + 12
  | none =>
    parts := parts ++ [textXml margin y 12 fpMuted on]
    y := y + 12
  parts := parts ++ fingerprintGrid bits shared fpSize cols cell margin y
  y := y + rows.toFloat * cell + 24
  parts := parts ++ [textXml margin y 12 fpMuted s!"bit 0 → bit {fpSize - 1}"]
  y := y + 8
  parts := parts ++ fingerprintBarcode bits shared fpSize W 56 margin y
  y := y + 56 + 22
  parts := parts ++ [rectXml margin (y - 9) 10 10 fpInk, textXml (margin + 16) y 12 fpMuted "on"]
  if other.isSome then
    parts := parts ++ [rectXml (margin + 52) (y - 9) 10 10 fpShared,
      textXml (margin + 68) y 12 fpMuted "also on in the compared molecule"]
  let H := y + margin
  let Wt := W + 2 * margin
  return .elem "svg" [("width", num Wt), ("height", num H), ("viewBox", s!"0 0 {num Wt} {num H}"),
    ("xmlns", "http://www.w3.org/2000/svg")] (rectXml 0 0 Wt H "#ffffff" :: parts)

/-- The fingerprint picture of a SMILES string, compared with `other` if given:
parsed with `SMILES.parseAromatized`, Morgan bits at `radius`, each labelled with
its SMILES. -/
def smilesFingerprintSvg (s : String) (other : Option String := none) (radius : ℕ := 2)
    (fpSize : ℕ := 2048) : Except String Xml := do
  let bitsOf (t : String) : Except String (List ℕ) := do
    let M ← SMILES.parseAromatized t
    return M.mol.morganBits radius fpSize
  let bits ← bitsOf s
  match other with
  | some t => return fingerprintSvg bits s (some (← bitsOf t, t)) fpSize
  | none => return fingerprintSvg bits s none fpSize

end LeanSMILES.Depict
