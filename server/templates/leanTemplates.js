const escapeLeanString = (s = '') => s.replace(/\\/g, '\\\\').replace(/"/g, '\\"')

export function explainParseError(constructorStr = '', message = '') {
  if (constructorStr.includes('ringAfterBranch ')) {
    return 'OpenSMILES §2.2 grammar requires ring-closure digits immediately after the atom (`atom ringbond* branch*`), before any branch `(...)`. Move the ring digit before the branch, e.g. `C1(C)CC1` instead of `C(C)1CC1`.'
  }
  if (constructorStr.includes('ringAfterBranchOpen')) {
    return 'A ring-closure digit cannot appear immediately after `(`. Attach it to an atom instead.'
  }
  if (constructorStr.includes('emptyBranch')) {
    return 'Empty branches `()` are invalid in OpenSMILES. Put at least one atom inside the parentheses.'
  }
  if (constructorStr.includes('unclosedBranch') || constructorStr.includes('unmatchedBranchClose')) {
    return 'Every opening parenthesis `(` for a branch must have a matching closing parenthesis `)`.'
  }
  if (constructorStr.includes('unclosedRing')) {
    return 'Every ring-closure digit must appear in pairs to open and close the cycle (e.g. `C1CCCCC1`).'
  }
  if (constructorStr.includes('conflictingRingBond')) {
    return 'OpenSMILES rejects conflicting bond symbols on the two ends of the same ring closure (e.g. `C=1CC-1`). Write the bond symbol on one end or use matching symbols.'
  }
  if (constructorStr.includes('selfBond')) {
    return 'A ring closure cannot connect an atom to itself (`src ≠ dst` is a type invariant of `Bond n`).'
  }
  if (constructorStr.includes('duplicateBond')) {
    return 'Two atoms cannot be joined by more than one bond (`nodup` invariant on `SimpleGraph (Fin n)`).'
  }
  if (constructorStr.includes('bondWithoutAtom')) {
    return 'A bond symbol (`-`, `=`, `#`, `$`, `:`) must sit between two atoms—never at the start, end, or twice in a row.'
  }
  if (constructorStr.includes('danglingDot')) {
    return 'The fragment separator `.` must separate two complete fragments and cannot appear at the start, end, or adjacent to parentheses.'
  }
  if (constructorStr.includes('badBracket')) {
    return 'Bracket atoms follow `[isotope? symbol chiral? hcount? charge? class?]` (OpenSMILES §3.1). Check hydrogen counts (single digit `H0`–`H9`), aromaticity, and class numbers.'
  }
  if (constructorStr.includes('unknownElement')) {
    return 'Unrecognized element symbol. Bare atoms must be in the organic subset (`B, C, N, O, P, S, F, Cl, Br, I, *`); all other 118 IUPAC elements must be written in brackets `[...]`.'
  }
  return `OpenSMILES syntax check failed: ${message}`
}

export const leanTemplates = {
  workerDaemon() {
    return `import LeanSMILES.SMILES.Canon
import LeanSMILES.Chem.Graph
import LeanSMILES.Chem.Charge
import LeanSMILES.Fingerprint.Morgan
import LeanSMILES.Aromaticity.Perceive
import LeanSMILES.Depict.Svg
import LeanSMILES.Data.CSVparser
import Lean.Data.Json

open LeanSMILES LeanSMILES.SMILES LeanSMILES.Molecule Lean

def tokenLabel (t : Token) : String :=
  match t.kind with
  | .atom a => a.toSmiles
  | .bond k => k.symbol
  | .dirBond d => s!"dir {repr d}"
  | .dot => "."
  | .branchOpen => "("
  | .branchClose => ")"
  | .ring k => s!"ring {k}"

def bondKindName : BondKind → String
  | .single => "single"
  | .double => "double"
  | .triple => "triple"
  | .quadruple => "quadruple"
  | .aromatic => "aromatic"

def ratStr (q : ℚ) : String :=
  if q.den == 1 then s!"{q.num}" else s!"{q.num}/{q.den}"

def runParse (s : String) : IO Unit := do
  match tokenize s, parse s with
  | .ok toks, .ok M =>
    let inRing := M.mol.inRingVector
    let B := M.mol.toBondMatrix
    let canon := M.canonicalSmiles
    let bits := M.morganBits
    let totalH := ((List.finRange M.n).map fun i => (M.mol.atom i).totalH).sum
    let dg := Depict.Graph.ofMol M
    let pos := Depict.layout dg
    let svgStr := (Depict.svgWith dg pos 36).render
    let coordsJson : Array Json := pos.map fun (x, y) => Json.mkObj [("x", toJson x), ("y", toJson y)]
    let atomsJson : Array Json := (List.finRange M.n).toArray.map fun i =>
      let a := M.mol.atom i
      let sym := match a.element with | some e => e.symbol | none => "*"
      Json.mkObj [
        ("idx", toJson i.val),
        ("raw", toJson a.toSmiles),
        ("symbol", toJson sym),
        ("degree", toJson (M.mol.degree i)),
        ("totalH", toJson a.totalH),
        ("charge", toJson a.charge),
        ("aromatic", toJson a.aromatic),
        ("inRing", toJson inRing[i])
      ]
    let bondsJson : Array Json := M.mol.bonds.toArray.map fun b =>
      Json.mkObj [
        ("src", toJson b.src.val),
        ("dst", toJson b.dst.val),
        ("kind", toJson (bondKindName b.kind))
      ]
    let toksJson : Array Json := toks.map fun t =>
      Json.mkObj [("pos", toJson t.pos), ("show", toJson (tokenLabel t))]
    let matJson : Array Json := (List.finRange M.n).toArray.map fun i =>
      toJson ((List.finRange M.n).toArray.map fun j => ratStr (B i j))
    let (chargeStatus, chargeLog) := match M.checkCharges with
      | .ok () => (Json.mkObj [("ok", toJson true)], "Except.ok ()")
      | .error msg => (Json.mkObj [("ok", toJson false), ("message", toJson msg)], s!"Except.error \\"{msg}\\"")
    let (aromStatus, aromLog) := match M.aromatize with
      | .ok MA =>
        let ac := MA.canonicalSmiles
        (Json.mkObj [("ok", toJson true), ("canonicalSmiles", toJson ac), ("morganBits", toJson MA.morganBits)],
         s!"Except.ok \\"{ac}\\"")
      | .error msg =>
        (Json.mkObj [("ok", toJson false), ("message", toJson msg)], s!"Except.error \\"{msg}\\"")
    let logs : Array String := #[
      s!"tokenize \\"{s}\\" --> Except.ok ({toks.size} tokens)",
      s!"parse \\"{s}\\" --> Except.ok (Molecule {M.n} : {M.n} atoms, {M.mol.numBonds} bonds, {totalH} H)",
      s!"(Mol.ofSmiles! \\"{s}\\").canonicalSmiles --> \\"{canon}\\"",
      s!"(Depict.svgWith dg pos 36).render --> 2D SVG ({svgStr.length} chars)",
      s!"M.checkCharges --> {chargeLog}",
      s!"M.aromatize --> {aromLog}",
      s!"M.morganBits 2 --> {bits} ({bits.length} on-bits)"
    ]
    let out := Json.mkObj [
      ("ok", toJson true),
      ("smiles", toJson s),
      ("canonicalSmiles", toJson canon),
      ("svg", toJson svgStr),
      ("coordinates", toJson coordsJson),
      ("n", toJson M.n),
      ("numBonds", toJson M.mol.numBonds),
      ("totalHydrogens", toJson totalH),
      ("isNormal", toJson M.isNormal),
      ("chargeCheck", chargeStatus),
      ("aromatized", aromStatus),
      ("tokens", toJson toksJson),
      ("atoms", toJson atomsJson),
      ("bonds", toJson bondsJson),
      ("adjMatrix", toJson matJson),
      ("morganBits", toJson bits),
      ("logs", toJson logs)
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"
  | _, .error e =>
    let logs : Array String := #[
      s!"parse \\"{s}\\" --> Except.error ({reprStr e})",
      s!"-- {toString e}"
    ]
    let out := Json.mkObj [
      ("ok", toJson false),
      ("error", toJson (toString e)),
      ("constructor", toJson (reprStr e)),
      ("isGrammarDeviation", toJson e.isGrammarDeviation),
      ("logs", toJson logs)
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"
  | .error e, _ =>
    let logs : Array String := #[
      s!"tokenize \\"{s}\\" --> Except.error ({reprStr e})",
      s!"-- {toString e}"
    ]
    let out := Json.mkObj [
      ("ok", toJson false),
      ("error", toJson (toString e)),
      ("constructor", toJson (reprStr e)),
      ("isGrammarDeviation", toJson e.isGrammarDeviation),
      ("logs", toJson logs)
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"

def runTanimoto (sA sB : String) : IO Unit := do
  match parse sA, parse sB with
  | .ok mA, .ok mB =>
    let bitsA := mA.morganBits
    let bitsB := mB.morganBits
    let shared := bitsA.filter bitsB.contains
    let unionCount := bitsA.length + bitsB.length - shared.length
    let q := tanimoto bitsA bitsB
    let score : Float := if unionCount == 0 then 1.0 else shared.length.toFloat / unionCount.toFloat
    let logs : Array String := #[
      s!"(Mol.ofSmiles! \\"{sA}\\").morganBits --> {bitsA.length} bits",
      s!"(Mol.ofSmiles! \\"{sB}\\").morganBits --> {bitsB.length} bits",
      s!"tanimoto bitsA bitsB --> {q.num} / {q.den} ({shared.length} shared of {unionCount} union)"
    ]
    let out := Json.mkObj [
      ("ok", toJson true),
      ("molA", Json.mkObj [("smiles", toJson sA), ("canonicalSmiles", toJson mA.canonicalSmiles), ("morganBits", toJson bitsA)]),
      ("molB", Json.mkObj [("smiles", toJson sB), ("canonicalSmiles", toJson mB.canonicalSmiles), ("morganBits", toJson bitsB)]),
      ("sharedBits", toJson shared),
      ("intersection", toJson shared.length),
      ("union", toJson unionCount),
      ("rational", toJson s!"{q.num} / {q.den}"),
      ("tanimoto", toJson score),
      ("logs", toJson logs)
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"
  | .error e, _ =>
    let out := Json.mkObj [
      ("ok", toJson false),
      ("error", toJson s!"Molecule A: {toString e}"),
      ("constructor", toJson (reprStr e))
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"
  | _, .error e =>
    let out := Json.mkObj [
      ("ok", toJson false),
      ("error", toJson s!"Molecule B: {toString e}"),
      ("constructor", toJson (reprStr e))
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"

def runDataset (datasetId : String) : IO Unit := do
  if datasetId == "delaney" then
    let path := "datasets/delaney-processed.csv"
    let records := CSVparser.load path
    let raw ← IO.FS.readFile path
    let lines := (raw.splitOn "\\n").map (fun l => (l.dropEndWhile (· == '\\r')).toString) |>.drop 1 |>.filter (fun l => !l.trimAscii.isEmpty)
    let slice := (lines.zip records.toList).take 30
    let rowsJson : Array Json := slice.toArray.map fun (line, recMol) =>
      let cells := CSVparser.splitLine line
      let name := (cells.getD 0 "").trimAscii.toString
      let logS := recMol.get .measuredLogSolubility
      let (atoms, bonds, canon) := match parse recMol.smiles with
        | .ok M => (M.n, M.mol.numBonds, M.canonicalSmiles)
        | .error _ => (0, 0, recMol.smiles)
      Json.mkObj [
        ("name", toJson name),
        ("smiles", toJson recMol.smiles),
        ("canonicalSmiles", toJson canon),
        ("atoms", toJson atoms),
        ("bonds", toJson bonds),
        ("metricLabel", toJson "Measured LogS"),
        ("metricValue", toJson logS)
      ]
    let logs : Array String := #[
      s!"let records := CSVparser.load \\"{path}\\" --> {records.size} molecules",
      s!"records[0] --> {reprStr (records.getD 0 default)}",
      s!"records.map (Mol.ofSmiles! ·.smiles).canonicalSmiles --> {rowsJson.size} rows evaluated"
    ]
    let out := Json.mkObj [
      ("ok", toJson true),
      ("datasetId", toJson datasetId),
      ("totalCount", toJson records.size),
      ("rows", toJson rowsJson),
      ("logs", toJson logs)
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"
  else if datasetId == "egfr-fda" then
    let path := "ench470-content/EGFR-FDA.csv"
    let raw ← IO.FS.readFile path
    let lines := (raw.splitOn "\\n").map (fun l => (l.dropEndWhile (· == '\\r')).toString) |>.filter (fun l => !l.trimAscii.isEmpty)
    let rowsJson : Array Json := lines.toArray.map fun line =>
      let cells := CSVparser.splitLine line
      let smi := (cells.getD 0 "").trimAscii.toString
      let name := (cells.getD 1 "").trimAscii.toString
      let (atoms, bonds, canon, bitsCount) := match parse smi with
        | .ok M => (M.n, M.mol.numBonds, M.canonicalSmiles, M.morganBits.length)
        | .error _ => (0, 0, smi, 0)
      Json.mkObj [
        ("name", toJson name),
        ("smiles", toJson smi),
        ("canonicalSmiles", toJson canon),
        ("atoms", toJson atoms),
        ("bonds", toJson bonds),
        ("metricLabel", toJson "Morgan Bits"),
        ("metricValue", toJson bitsCount)
      ]
    let logs : Array String := #[
      s!"CSVparser.splitLine \\"{path}\\" --> {lines.length} FDA-approved EGFR inhibitors",
      s!"lines.map (Mol.ofSmiles! ·).canonicalSmiles --> {lines.length} molecules evaluated"
    ]
    let out := Json.mkObj [
      ("ok", toJson true),
      ("datasetId", toJson datasetId),
      ("totalCount", toJson lines.length),
      ("rows", toJson rowsJson),
      ("logs", toJson logs)
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"
  else if datasetId == "egfr-actives" then
    let path := "ench470-content/Chembl_EGFR_actives_ML.csv"
    let raw ← IO.FS.readFile path
    let lines := (raw.splitOn "\\n").map (fun l => (l.dropEndWhile (· == '\\r')).toString) |>.drop 1 |>.filter (fun l => !l.trimAscii.isEmpty)
    let slice := lines.take 25
    let rowsJson : Array Json := slice.toArray.map fun line =>
      let cells := CSVparser.splitLine line
      let smi := (cells.getD 0 "").trimAscii.toString
      let chemblId := (cells.getD 1 "").trimAscii.toString
      let (atoms, bonds, canon, bitsCount) := match parse smi with
        | .ok M => (M.n, M.mol.numBonds, M.canonicalSmiles, M.morganBits.length)
        | .error _ => (0, 0, smi, 0)
      Json.mkObj [
        ("name", toJson chemblId),
        ("smiles", toJson smi),
        ("canonicalSmiles", toJson canon),
        ("atoms", toJson atoms),
        ("bonds", toJson bonds),
        ("metricLabel", toJson "Morgan Bits"),
        ("metricValue", toJson bitsCount)
      ]
    let logs : Array String := #[
      s!"CSVparser.splitLine \\"{path}\\" --> {lines.length} ChEMBL EGFR active compounds",
      s!"slice.map (Mol.ofSmiles! ·).canonicalSmiles --> {rowsJson.size} molecules evaluated"
    ]
    let out := Json.mkObj [
      ("ok", toJson true),
      ("datasetId", toJson datasetId),
      ("totalCount", toJson lines.length),
      ("rows", toJson rowsJson),
      ("logs", toJson logs)
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"
  else
    let path := "ench470-content/ThermoPropertiesSMILES.csv"
    let raw ← IO.FS.readFile path
    let lines := (raw.splitOn "\\n").map (fun l => (l.dropEndWhile (· == '\\r')).toString) |>.drop 1 |>.filter (fun l => !l.trimAscii.isEmpty)
    let slice := lines.take 25
    let rowsJson : Array Json := slice.toArray.map fun line =>
      let cells := CSVparser.splitLine line
      let name := (cells.getD 0 "").trimAscii.toString
      let mw := (cells.getD 1 "").trimAscii.toString
      let bp := (cells.getD 4 "").trimAscii.toString
      let smi := (cells.getD 6 "").trimAscii.toString
      let (atoms, bonds, canon) := match parse smi with
        | .ok M => (M.n, M.mol.numBonds, M.canonicalSmiles)
        | .error _ => (0, 0, smi)
      Json.mkObj [
        ("name", toJson name),
        ("smiles", toJson smi),
        ("canonicalSmiles", toJson canon),
        ("atoms", toJson atoms),
        ("bonds", toJson bonds),
        ("metricLabel", toJson s!"BP (K) · MW {mw}"),
        ("metricValue", toJson bp)
      ]
    let logs : Array String := #[
      s!"CSVparser.splitLine \\"{path}\\" --> {lines.length} fluid compounds",
      s!"slice.map (Mol.ofSmiles! ·).canonicalSmiles --> {rowsJson.size} molecules evaluated"
    ]
    let out := Json.mkObj [
      ("ok", toJson true),
      ("datasetId", toJson "thermo"),
      ("totalCount", toJson lines.length),
      ("rows", toJson rowsJson),
      ("logs", toJson logs)
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return ()
  let parts := line.trimAscii.toString.splitOn "\\t"
  match parts with
  | ["parse", s] =>
    runParse s
    stdout.flush
  | ["tanimoto", a, b] =>
    runTanimoto a b
    stdout.flush
  | ["dataset", d] =>
    runDataset d
    stdout.flush
  | _ =>
    IO.println "__JSON_START__{\\"ok\\":false,\\"error\\":\\"Unknown command\\"}__JSON_END__"
    stdout.flush
  loop stdin stdout

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  IO.println "__WORKER_READY__"
  stdout.flush
  loop stdin stdout
  return 0
`
  },

  parseMolecule(smiles) {
    return `parse\t${escapeLeanString(smiles)}`
  },

  compareTanimoto(smilesA, smilesB) {
    return `tanimoto\t${escapeLeanString(smilesA)}\t${escapeLeanString(smilesB)}`
  },

  loadDataset(datasetId = 'delaney') {
    return `dataset\t${escapeLeanString(datasetId)}`
  },
}
