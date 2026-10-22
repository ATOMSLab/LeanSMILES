/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ejike89
-/
module

public import LeanSMILES.SMILES.Parse
public import LeanSMILES.Depict.Svg

/-!
# LeanSMILES.Depict.Cli

The `depict` executable (root `LeanSMILES.Depict.Main`): drawings from the
command line.

```
lake exe depict "C[C@H](N)C(=O)O"            SVG on standard output
lake exe depict "C[C@H](N)C(=O)O" out.svg    …or into a file
lake exe depict --mol "F/C=C/F"              MDL mol block (wedge/hash flags)
lake exe depict --html in.smi out.html       a gallery page, one SMILES per line
lake exe depict --sdf in.smi out.sdf         mol blocks of every line, SMILES as
                                             title, for tools/check_depiction.py
```
-/

@[expose] public section

open LeanSMILES LeanSMILES.SMILES

namespace LeanSMILES.Depict

/-- Usage text. -/
def usage : String :=
  "\n".intercalate [
    "usage:",
    "  lake exe depict <smiles> [out.svg]         SVG drawing",
    "  lake exe depict --mol <smiles>             MDL mol block with wedge/hash flags",
    "  lake exe depict --html <in.smi> <out.html> gallery of one SMILES per line",
    "  lake exe depict --sdf <in.smi> <out.sdf>   mol blocks for tools/check_depiction.py"]

/-- The SMILES on each non-empty, non-comment line of a `.smi` file (the first
whitespace-separated field). -/
def readSmi (path : String) : IO (Array String) := do
  let lines ← IO.FS.lines path
  return lines.filterMap fun l ↦
    let s := l.trimAscii.toString
    if s.isEmpty || s.startsWith "#" then none
    else (s.splitOn " ").head?.map fun w ↦ w.trimAscii.toString

/-- A gallery page of drawings. -/
def gallery (smiles : Array String) : String :=
  let cards := smiles.toList.map fun s ↦
    let body := match parse s with
      | .ok M => (M.svg 28).render
      | .error e => s!"<p style=\"color:#b02a37\">{Xml.escape (toString e)}</p>"
    s!"<div style=\"display:inline-block;margin:6px;padding:8px;border:1px solid #ddd;\
      border-radius:6px;vertical-align:top;background:#fff\">{body}\
      <div style=\"font:11px monospace;max-width:260px;overflow-wrap:anywhere\">\
      {Xml.escape s}</div></div>"
  "<!doctype html><html><head><meta charset=\"utf-8\"><title>LeanSMILES depictions\
  </title></head><body style=\"font-family:system-ui,sans-serif;background:#f6f8fa;\
  margin:16px\">" ++ String.join cards ++ "</body></html>"

/-- Mol blocks of every SMILES, each preceded by its SMILES on a line of its own
and followed by `$$$$`; a line `ERROR: …` where the SMILES does not parse. -/
def sdf (smiles : Array String) : String :=
  String.join <| smiles.toList.map fun s ↦
    match parse s with
    | .ok M => s!"{s}\n{M.molBlock}$$$$\n"
    | .error e => s!"{s}\nERROR: {e}\n$$$$\n"

/-- Entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--mol", s] =>
    match parse s with
    | .ok M => IO.print M.molBlock; return 0
    | .error e => IO.eprintln s!"{e}"; return 1
  | ["--html", inp, out] =>
    IO.FS.writeFile out (gallery (← readSmi inp))
    IO.println s!"wrote {out}"
    return 0
  | ["--sdf", inp, out] =>
    IO.FS.writeFile out (sdf (← readSmi inp))
    IO.println s!"wrote {out}"
    return 0
  | [s] | [s, _] =>
    if s.startsWith "--" then IO.println usage; return 1 else
    match parse s with
    | .error e => IO.eprintln s!"{e}"; return 1
    | .ok M =>
      let svg := M.svgString
      match args with
      | [_, out] => IO.FS.writeFile out svg; IO.println s!"wrote {out}"
      | _ => IO.println svg
      return 0
  | _ => IO.println usage; return 1

end LeanSMILES.Depict
