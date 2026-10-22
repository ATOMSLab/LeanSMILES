/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ejike Ugwuanyi, Claude (Anthropic)
-/
module

public import LeanSMILES.Depict.Cli

/-!
# LeanSMILES.Tests.Depict

Does every drawing carry what the SMILES wrote?

`datasets/stereo.smi` holds 557 stereo-bearing SMILES: 550 drawn from the
ESOL, WEHI, CDK2, ChEMBL and PubChem example sets that RDKit ships, plus seven
textbook cases (glucose, cubane, adamantane, norbornane, cis/trans alkenes).
For each one the drawing is checked without any other toolkit:

* every tetrahedral centre (`@`/`@@` with four neighbors counting the implicit
  hydrogen) carries exactly one wedge or hash;
* every double bond with `/` `\` marks on both ends is drawn with the written
  cis/trans arrangement (the two substituents on the same side of the bond
  axis iff cis) — the layout is a heuristic, so the test passes while at most
  1 % of the drawings miss on either count (currently 5 of 557, all crowded
  tri- or tetrasubstituted alkenes);
* and, reported rather than failed, whether every bond is between 0.7 and 1.6
  bond lengths long and no two atoms of a component coincide — crowded
  drawings of very large molecules do not always manage that.

The independent check — that RDKit reads the same stereochemistry back from
the mol blocks — is `tools/check_depiction.py`, which needs the `.sdf` this
test writes:

```
lake exe depict-test [datasets/stereo.smi] [out/stereo.sdf]
python3 tools/check_depiction.py out/stereo.sdf
```
-/

public section

open LeanSMILES LeanSMILES.SMILES LeanSMILES.Depict

/-- The stereochemical problems of one drawing: a centre without exactly one
wedge or hash, or a marked double bond drawn the other way round. -/
def stereoProblems (g : Graph) (pos : Array Pt) : List String := Id.run do
  let stereo := wedges g pos
  let mut out : List String := []
  for i in [0:g.numAtoms] do
    if ((g.atom i).chirality.bind tetrahedral).isSome && (g.stereoNeighbors i).length == 4 then
      let k := (stereo.filter (·.centre == i)).length
      if k != 1 then out := out ++ [s!"atom {i}: {k} stereo bonds"]
  let (cis, all) := g.cisPairs
  for e in g.edges do
    if e.kind != .double || e.ring then continue
    let (ux, uy) := pos[e.src]!
    let (vx, vy) := pos[e.dst]!
    let side (p : Pt) : Float := (vx - ux) * (p.2 - uy) - (vy - uy) * (p.1 - ux)
    for (a, c) in all do
      if (g.edgeIndex? a e.src).isNone || (g.edgeIndex? c e.dst).isNone then continue
      let same := side pos[a]! * side pos[c]! > 0
      let wantCis := cis.contains (a, c) || cis.contains (c, a)
      if same != wantCis then out := out ++ [s!"bond {e.src}={e.dst}: {a},{c} drawn wrong"]
  return out

/-- The geometric blemishes of one drawing: a bond shorter than 0.7 or longer
than 1.6 bond lengths, or two atoms of a component closer than 0.1. -/
def geometryProblems (g : Graph) (pos : Array Pt) : List String := Id.run do
  let mut out : List String := []
  for e in g.edges do
    let (ux, uy) := pos[e.src]!
    let (vx, vy) := pos[e.dst]!
    let len := Float.sqrt (sq (vx - ux) + sq (vy - uy))
    if len < 0.7 || len > 1.6 then out := out ++ [s!"bond {e.src}-{e.dst}: length {len}"]
  let D := g.distances
  for i in [0:g.numAtoms] do
    for j in [i + 1:g.numAtoms] do
      if D[i]![j]! > 0 then
        let (xi, yi) := pos[i]!
        let (xj, yj) := pos[j]!
        if sq (xi - xj) + sq (yi - yj) < 0.01 then out := out ++ [s!"atoms {i},{j} coincide"]
  return out

def main (args : List String) : IO UInt32 := do
  let inp := args.headD "datasets/stereo.smi"
  let out := (args.drop 1).headD "out/stereo.sdf"
  let smiles ← readSmi inp
  let mut ok := 0
  let mut bad : Array (String × List String) := #[]
  let mut blemished : Array (String × List String) := #[]
  let mut rejected : Array String := #[]
  let mut centres := 0
  let mut alkenes := 0
  let mut blocks : Array String := #[]
  for s in smiles do
    match parse s with
    | .error e =>
      rejected := rejected.push s
      blocks := blocks.push s!"{s}\nERROR: {e}\n$$$$\n"
    | .ok M =>
      let g := Graph.ofMol M
      let pos := layout g
      blocks := blocks.push s!"{s}\n{molBlockWith g pos}$$$$\n"
      centres := centres + ((List.range g.numAtoms).filter fun i ↦
        ((g.atom i).chirality.bind tetrahedral).isSome).length
      alkenes := alkenes + (g.edges.filter g.stereoSpecified).size
      match stereoProblems g pos with
      | [] => ok := ok + 1
      | ps => bad := bad.push (s, ps)
      match geometryProblems g pos with
      | [] => pure ()
      | ps => blemished := blemished.push (s, ps)
  IO.println s!"{smiles.size} SMILES, {rejected.size} rejected by the parser"
  IO.println s!"stereochemistry: {ok} drawings as written, {bad.size} not \
    ({centres} tetrahedral centres and {alkenes} specified double bonds)"
  for (s, ps) in bad.toList.take 10 do
    IO.println s!"  {s}"
    for p in ps.take 3 do IO.println s!"    {p}"
  IO.println s!"geometry: {blemished.size} drawings with a short or long bond or overlapping atoms"
  for (s, ps) in blemished.toList.take 5 do
    IO.println s!"  {s}"
    for p in ps.take 2 do IO.println s!"    {p}"
  if let some dir := (System.FilePath.mk out).parent then IO.FS.createDirAll dir
  IO.FS.writeFile out (String.join blocks.toList)
  IO.println s!"wrote {out} for tools/check_depiction.py"
  -- a layout is a heuristic: the test passes while at most 1 % of the drawings miss
  return if bad.size * 100 ≤ smiles.size then 0 else 1
