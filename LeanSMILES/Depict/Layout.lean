/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ejike Ugwuanyi
-/
module

public import LeanSMILES.Depict.Graph

/-!
# LeanSMILES.Depict.Layout

2D coordinates for a molecule, deterministic and dependency-free:

1. all-pairs graph distances (`Graph.distances`);
2. **classical multidimensional scaling** to initialise: the two leading
   eigenvectors of the double-centred squared-distance matrix, by power
   iteration (`layoutComponent`);
3. **stress majorisation** (Gansner, Koren & North 2004: localized updates
   with weights `1/d²`), so bonded atoms sit at unit distance, chains zigzag
   and rings become regular polygons;
4. orientation along the principal axes, components side by side;
5. **cis/trans**: substituent pairs that `/` `\` specify get their own target
   distance and extra weight, and a double bond that still came out the wrong
   way round has one side reflected across its axis (`fixDoubleBonds`);
6. **cages**: a component with three or more rings whose flat layout misfits
   its short distances by more than 15 % is laid out in three dimensions and
   projected obliquely (`layoutCage`), which is how chemists draw cubane,
   adamantane or norbornane;
7. **tetrahedral centres**: for every `@`/`@@` atom one bond is drawn as a
   wedge or a hash, chosen so that the drawn configuration has the written
   chirality, which `wedges` checks by the signed volume of the neighbors
   in SMILES order.

Coordinates are in bond lengths, `y` up.
-/

@[expose] public section

namespace LeanSMILES.Depict

/-- A point in the plane. -/
abbrev Pt := Float × Float

/-- `x²`. -/
def sq (x : Float) : Float := x * x

/-- Maximum of two floats. -/
def fmax (a b : Float) : Float := if a < b then b else a

/-- Minimum of two floats. -/
def fmin (a b : Float) : Float := if a < b then a else b

/-- Target distance for atoms `k` bonds apart: the span of an ideal 120°
zigzag (`k·√3/2` for even `k`, `√((k·√3/2)² + 1/4)` for odd `k`), so that
chains zigzag and rings stay regular. -/
def zigzag (k : ℕ) : Float :=
  let x := k.toFloat * 0.8660254
  if k % 2 == 0 then x else Float.sqrt (x * x + 0.25)

/-- Power iteration for the leading eigenvectors of a symmetric matrix `B`
(given as a function), deflating the ones already found. Returns
`(eigenvector, eigenvalue)` pairs. -/
def leadingEigen (k : ℕ) (mulB : Array Float → Array Float) (count : ℕ) (iters : ℕ := 150) :
    Array (Array Float × Float) := Id.run do
  let dot (u v : Array Float) : Float := (Array.range k).foldl (fun s j ↦ s + u[j]! * v[j]!) 0
  let normalize (v : Array Float) : Array Float :=
    let n := Float.sqrt (dot v v); if n == 0 then v else v.map (· / n)
  let mut found : Array (Array Float × Float) := #[]
  for t in [0:count] do
    let mut v :=
      normalize ((Array.range k).map fun j ↦ ((t.toFloat + 1.3) * j.toFloat + 0.7).sin + 0.05)
    for _ in [0:iters] do
      let mut w := mulB v
      for (u, _) in found do
        let c := dot w u
        w := (Array.range k).map fun j ↦ w[j]! - c * u[j]!
      v := normalize w
    found := found.push (v, dot v (mulB v))
  return found

/-- The classical-MDS matrix `B = −½ J D² J` for target distances `d`, as a
function on vectors. -/
def mdsOperator (k : ℕ) (d : ℕ → ℕ → Float) : Array Float → Array Float :=
  let D2 : Array (Array Float) :=
    (Array.range k).map fun a ↦ (Array.range k).map fun b ↦ sq (d a b)
  let rowMean := D2.map fun r ↦ r.foldl (· + ·) 0 / k.toFloat
  let tot := rowMean.foldl (· + ·) 0 / k.toFloat
  let B : Array (Array Float) := (Array.range k).map fun a ↦ (Array.range k).map fun b ↦
    -0.5 * (D2[a]![b]! - rowMean[a]! - rowMean[b]! + tot)
  fun v ↦ B.map fun r ↦ (Array.range k).foldl (fun s j ↦ s + r[j]! * v[j]!) 0

/-- Lay out one component (the atoms `idx`) in the plane, unit bond length.
Pairs in `cis` are placed two bond lengths apart instead of 2.65; pairs in
`specified` get extra weight. -/
def layoutComponent (D : Array (Array ℕ)) (idx : Array ℕ) (cis : List (ℕ × ℕ) := [])
    (specified : List (ℕ × ℕ) := []) : Array Pt := Id.run do
  let k := idx.size
  if k == 1 then return #[(0, 0)]
  if k == 2 then return #[(0, 0), (1, 0)]
  let d (a b : ℕ) : Float :=
    let (i, j) := (idx[a]!, idx[b]!)
    if cis.contains (i, j) || cis.contains (j, i) then 2.0 else zigzag (D[i]![j]!)
  let isSpecified (a b : ℕ) : Bool :=
    let (i, j) := (idx[a]!, idx[b]!)
    specified.contains (i, j) || specified.contains (j, i)
  -- classical MDS initialisation
  let eig := leadingEigen k (mdsOperator k d) 2
  let (v1, l1) := eig[0]!
  let (v2, l2) := eig[1]!
  let s1 := Float.sqrt (fmax l1 0.01)
  let s2 := Float.sqrt (fmax l2 0.01)
  let mut X : Array Pt := (Array.range k).map fun j ↦ (v1[j]! * s1, v2[j]! * s2)
  -- stress majorisation: targets and weights precomputed once
  let T : Array (Array Float) := (Array.range k).map fun a ↦ (Array.range k).map fun b ↦ d a b
  let Wt : Array (Array Float) := (Array.range k).map fun a ↦ (Array.range k).map fun b ↦
    let dab := T[a]![b]!
    if dab ≤ 0 then 0 else if isSpecified a b then 1.5 else 1 / (dab * dab)
  -- at most 300 sweeps, stopping once no atom moves more than 10⁻⁴
  for _ in [0:300] do
    let mut moved := 0.0
    for a in [0:k] do
      let mut nx := 0.0
      let mut ny := 0.0
      let mut ws := 0.0
      let (xa, ya) := X[a]!
      let Ta := T[a]!
      let Wa := Wt[a]!
      for b in [0:k] do
        if a != b then
          let dab := Ta[b]!
          let w := Wa[b]!
          if w > 0 then
            let (xb, yb) := X[b]!
            let dx := xa - xb
            let dy := ya - yb
            let dist := fmax (Float.sqrt (dx * dx + dy * dy)) 1e-6
            nx := nx + w * (xb + dab * dx / dist)
            ny := ny + w * (yb + dab * dy / dist)
            ws := ws + w
      if ws > 0 then
        let p : Pt := (nx / ws, ny / ws)
        moved := fmax moved (Float.abs (p.1 - xa) + Float.abs (p.2 - ya))
        X := X.set! a p
    if moved < 1e-4 then break
  -- principal axes: rotate so the long axis is horizontal
  let cx := X.foldl (fun s p ↦ s + p.1) 0 / k.toFloat
  let cy := X.foldl (fun s p ↦ s + p.2) 0 / k.toFloat
  let sxx := X.foldl (fun s p ↦ s + sq (p.1 - cx)) 0
  let syy := X.foldl (fun s p ↦ s + sq (p.2 - cy)) 0
  let sxy := X.foldl (fun s p ↦ s + (p.1 - cx) * (p.2 - cy)) 0
  let θ := 0.5 * Float.atan2 (2 * sxy) (sxx - syy)
  let (c, s) := (Float.cos θ, Float.sin θ)
  return X.map fun (x, y) ↦ ((x - cx) * c + (y - cy) * s, -(x - cx) * s + (y - cy) * c)

/-- 3D layout of a cage-like component (classical MDS in three dimensions,
then 3D stress majorisation) projected obliquely: the usual perspective
drawings of cubane, adamantane and other polycyclic cages. -/
def layoutCage (D : Array (Array ℕ)) (idx : Array ℕ) : Array Pt := Id.run do
  let k := idx.size
  let d (a b : ℕ) : Float := zigzag (D[idx[a]!]![idx[b]!]!)
  let eig := leadingEigen k (mdsOperator k d) 3 200
  let sc (t : ℕ) : Float := Float.sqrt (fmax (eig[t]!).2 0.01)
  let mut X : Array (Float × Float × Float) := (Array.range k).map fun j ↦
    ((eig[0]!).1[j]! * sc 0, (eig[1]!).1[j]! * sc 1, (eig[2]!).1[j]! * sc 2)
  for _ in [0:200] do
    let mut moved := 0.0
    for a in [0:k] do
      let mut nx := 0.0
      let mut ny := 0.0
      let mut nz := 0.0
      let mut ws := 0.0
      let (xa, ya, za) := X[a]!
      for b in [0:k] do
        if a != b then
          let dab := d a b
          if dab > 0 then
            let w := 1 / (dab * dab)
            let (xb, yb, zb) := X[b]!
            let (dx, dy, dz) := (xa - xb, ya - yb, za - zb)
            let dist := fmax (Float.sqrt (dx * dx + dy * dy + dz * dz)) 1e-6
            nx := nx + w * (xb + dab * dx / dist)
            ny := ny + w * (yb + dab * dy / dist)
            nz := nz + w * (zb + dab * dz / dist)
            ws := ws + w
      if ws > 0 then
        moved := fmax moved (Float.abs (nx / ws - xa) + Float.abs (ny / ws - ya) +
          Float.abs (nz / ws - za))
        X := X.set! a (nx / ws, ny / ws, nz / ws)
    if moved < 1e-4 then break
  -- oblique (cabinet) projection
  return X.map fun (x, y, z) ↦ (x + 0.45 * z, y + 0.3 * z)

/-- Is a flat layout a poor fit? At least three rings, and the mean relative
error of the distances between atoms at most two bonds apart above 15 %. -/
def cageLike (D : Array (Array ℕ)) (idx : Array ℕ) (X : Array Pt) (nRings : ℕ) : Bool :=
  Id.run do
  if nRings < 3 then return false
  let k := idx.size
  let mut err := 0.0
  let mut cnt := 0.0
  for a in [0:k] do
    for b in [a + 1:k] do
      let g := D[idx[a]!]![idx[b]!]!
      if g == 1 || g == 2 then
        let target := if g == 1 then 1.0 else 1.7320508
        let (xa, ya) := X[a]!
        let (xb, yb) := X[b]!
        let dist := Float.sqrt (sq (xa - xb) + sq (ya - yb))
        err := err + Float.abs (dist - target) / target
        cnt := cnt + 1
  return cnt > 0 && err / cnt > 0.15

/-- Enforce the written cis/trans arrangement: a non-ring double bond drawn
the wrong way round has its `dst` side reflected across the bond axis (the
stress layout alone can be trapped in the other configuration). -/
def fixDoubleBonds (g : Graph) (pos : Array Pt) : Array Pt := Id.run do
  let mut pos := pos
  for e in g.edges do
    if e.kind != .double || e.ring then continue
    let du := (g.dirSides e.src).filter (·.1 != e.dst)
    let dv := (g.dirSides e.dst).filter (·.1 != e.src)
    match du, dv with
    | (a, sa) :: _, (c, sc) :: _ =>
      let (ux, uy) := pos[e.src]!
      let (vx, vy) := pos[e.dst]!
      let (dx, dy) := (vx - ux, vy - uy)
      let side (p : Pt) : Float := dx * (p.2 - uy) - dy * (p.1 - ux)
      let sameSide := side pos[a]! * side pos[c]! > 0
      if sameSide != (sa == sc) then
        let len2 := fmax (dx * dx + dy * dy) 1e-9
        let mask := g.sideOf e.src e.dst e.dst
        for i in [0:g.numAtoms] do
          if mask[i]! then
            let (px, py) := pos[i]!
            let t := ((px - ux) * dx + (py - uy) * dy) / len2
            let (fx, fy) := (ux + t * dx, uy + t * dy)
            pos := pos.set! i (2 * fx - px, 2 * fy - py)
    | _, _ => pure ()
  return pos

/-- Coordinates for every atom, in bond lengths with `y` up; components are
placed left to right. -/
def layout (g : Graph) : Array Pt := Id.run do
  let D := g.distances
  let (cis, specified) := g.cisPairs
  let mut pos : Array Pt := Array.replicate g.numAtoms (0, 0)
  let mut offset := 0.0
  let nRings := g.ringCount
  for comp in g.components do
    let idx := comp.toArray
    let X2 := layoutComponent D idx cis specified
    let X := if cageLike D idx X2 nRings then layoutCage D idx else X2
    let minX := X.foldl (fun s p ↦ fmin s p.1) 1e9
    let maxX := X.foldl (fun s p ↦ fmax s p.1) (-1e9)
    for j in [0:idx.size] do
      let (x, y) := X[j]!
      pos := pos.set! idx[j]! (x - minX + offset, y)
    offset := offset + (maxX - minX) + 1.5
  return fixDoubleBonds g pos

/-- A stereo bond of the drawing: the centre (narrow end), the neighbor it
points to, and whether it is a wedge (`true`) or a hash (`false`). -/
structure StereoBond where
  /-- The stereocentre. -/
  centre : ℕ
  /-- The neighbor drawn out of the plane. -/
  neighbor : ℕ
  /-- Wedge (towards the viewer) or hash (away). -/
  wedge : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Signed volume of the tetrahedron spanned by four points,
`(p₂ − p₁) · ((p₃ − p₁) × (p₄ − p₁))`. -/
def signedVolume (p1 p2 p3 p4 : Float × Float × Float) : Float :=
  let sub (u v : Float × Float × Float) : Float × Float × Float :=
    (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)
  let (ax, ay, az) := sub p2 p1
  let (bx, by', bz) := sub p3 p1
  let (cx, cy, cz) := sub p4 p1
  ax * (by' * cz - bz * cy) - ay * (bx * cz - bz * cx) + az * (bx * cy - by' * cx)

/-- Whether a chirality mark is the tetrahedral anticlockwise (`@`, `@TH1`) or
clockwise (`@@`, `@TH2`) one; `none` for the other classes, which are not
drawn. -/
def tetrahedral : Chirality → Option Bool
  | .anticlockwise => some true
  | .clockwise => some false
  | .th ⟨0, _⟩ => some true
  | .th ⟨1, _⟩ => some false
  | _ => none

/-- Wedge or hash bonds for the tetrahedral stereocentres. For each `@`/`@@`
atom one neighbor — preferably terminal, not in a ring, not itself a centre
and not already carrying a stereo bond — is drawn out of the plane, and wedge
or hash is chosen so that the drawn configuration has the written chirality:
`@` means that, looking from the first neighbor in SMILES order, the other
three run anticlockwise, i.e. the signed volume of the four neighbors is
negative when the raised one is given `z = 1` and the implicit hydrogen
`z = −1`. -/
def wedges (g : Graph) (pos : Array Pt) : List StereoBond := Id.run do
  let mut out : List StereoBond := []
  for i in [0:g.numAtoms] do
    let a := g.atom i
    let some tag := a.chirality | continue
    -- only the tetrahedral marks: `@` and `@TH1` anticlockwise, `@@` and `@TH2` clockwise
    let some anticlockwise := tetrahedral tag | continue
    let nbrs := g.stereoNeighbors i
    if nbrs.length != 4 then continue
    let real := nbrs.filterMap id
    if real.isEmpty then continue
    let used (j : ℕ) : Bool := out.any fun s ↦
      (s.centre == i && s.neighbor == j) || (s.centre == j && s.neighbor == i)
    let score (j : ℕ) : ℕ :=
      (if g.kindBetween i j != .single then 100 else 0) + (if used j then 100 else 0) +
      (if (g.atom j).chirality.isSome then 50 else 0) +
      (if g.inRing i j then 10 else 0) + (if g.degree j > 1 then 1 else 0)
    let j := real.foldl (fun best j ↦ if score j < score best then j else best) real.head!
    let (cx, cy) := pos[i]!
    let p3 (x : Option ℕ) : Float × Float × Float := match x with
      | some k => let (x, y) := pos[k]!; (x, y, if k == j then 1 else 0)
      | none => (cx, cy, -1)
    let det : Float := match nbrs with
      | [a, b, c, d] => signedVolume (p3 a) (p3 b) (p3 c) (p3 d)
      | _ => 0
    out := ⟨i, j, (det < 0) == anticlockwise⟩ :: out
  return out

end LeanSMILES.Depict
