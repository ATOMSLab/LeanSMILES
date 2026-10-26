const cleanCmdField = (s = '') => String(s).replace(/[\t\r\n]/g, '')

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
import LeanLearn.Regression.SparseRidge
import LeanLearn.Regression.RidgeFloat
import LeanLearn.Regression.OLSFloat
import LeanLearn.Regression.Metrics
import LeanLearn.Regression.Solvers
import LeanLearn.Regression.Certificates
import LeanLearn.Plot.Parity
import LeanLearn.Classification.Logistic
import LeanLearn.Classification.ROC
import Pipelines.Representation
import Pipelines.Pipeline
import Pipelines.Certificates
import Lean.Data.Json

open LeanSMILES LeanSMILES.SMILES LeanSMILES.Molecule Lean
open LeanLearn LeanLearn.Regression LeanLearn.Plot LeanLearn.Classification Pipelines

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

def parseSigned? (s : String) : Option Float :=
  let s := s.trimAscii.toString
  if s.isEmpty then none else
  let neg := s.startsWith "-"
  let body := if neg then (s.drop 1).toString else if s.startsWith "+" then (s.drop 1).toString else s
  match body.splitOn "." with
  | [i, f] =>
    match (i ++ f).toNat? with
    | some n => some (if neg then -Float.ofScientific n true f.length else Float.ofScientific n true f.length)
    | none => none
  | [i] =>
    match i.toNat? with
    | some n => some (if neg then -n.toFloat else n.toFloat)
    | none => none
  | _ => none

def parseRat (s : String) : ℚ :=
  let s := s.trimAscii.toString
  let neg := s.startsWith "-"
  let body := if neg then (s.drop 1).toString else if s.startsWith "+" then (s.drop 1).toString else s
  let q : ℚ := match body.splitOn "." with
    | [i, f] =>
      let num : ℕ := (i ++ f).toNat?.getD 0
      let den : ℕ := 10 ^ f.length
      (num : ℚ) / (den : ℚ)
    | [i] => (i.toNat?.getD 0 : ℚ)
    | _ => 0
  if neg then -q else q

def rocSvg (title subtitle : String) (curve : Array (Float × Float)) (aucVal : Float) : String := Id.run do
  let (W, H, L, R, T) := ((600 : Float), (640 : Float), (78 : Float), (26 : Float), (92 : Float))
  let size := W - L - R
  let sx (v : Float) := L + v * size
  let sy (v : Float) := T + size - v * size
  let c (v : Float) := fixed v 1
  let mut out := s!"<svg xmlns=\\"http://www.w3.org/2000/svg\\" viewBox=\\"0 0 {c W} {c H}\\" width=\\"{c W}\\" height=\\"{c H}\\" font-family=\\"Helvetica, Arial, sans-serif\\">\\n"
  out := out ++ s!"<rect width=\\"{c W}\\" height=\\"{c H}\\" fill=\\"#ffffff\\"/>\\n"
  out := out ++ s!"<text x=\\"{c L}\\" y=\\"34\\" font-size=\\"19\\" font-weight=\\"700\\" fill=\\"#172026\\">{title}</text>\\n"
  out := out ++ s!"<text x=\\"{c L}\\" y=\\"56\\" font-size=\\"13\\" fill=\\"#5b6a73\\">{subtitle}</text>\\n"
  for k in [0:6] do
    let v := k.toFloat * 0.2
    out := out ++ s!"<line x1=\\"{c (sx v)}\\" y1=\\"{c T}\\" x2=\\"{c (sx v)}\\" y2=\\"{c (T + size)}\\" stroke=\\"#e3e9ec\\"/>\\n"
    out := out ++ s!"<line x1=\\"{c L}\\" y1=\\"{c (sy v)}\\" x2=\\"{c (L + size)}\\" y2=\\"{c (sy v)}\\" stroke=\\"#e3e9ec\\"/>\\n"
    out := out ++ s!"<text x=\\"{c (sx v)}\\" y=\\"{c (T + size + 20)}\\" font-size=\\"12\\" text-anchor=\\"middle\\" fill=\\"#5b6a73\\">{fixed v 1}</text>\\n"
    out := out ++ s!"<text x=\\"{c (L - 10)}\\" y=\\"{c (sy v + 4)}\\" font-size=\\"12\\" text-anchor=\\"end\\" fill=\\"#5b6a73\\">{fixed v 1}</text>\\n"
  out := out ++ s!"<line x1=\\"{c (sx 0)}\\" y1=\\"{c (sy 0)}\\" x2=\\"{c (sx 1)}\\" y2=\\"{c (sy 1)}\\" stroke=\\"#9fb0b9\\" stroke-width=\\"1.2\\" stroke-dasharray=\\"5 4\\"/>\\n"
  if curve.size > 1 then
    let ptsStr := String.intercalate " " (curve.toList.map fun (x, y) => s!"{c (sx x)},{c (sy y)}")
    let areaStr := s!"{c (sx 0)},{c (sy 0)} " ++ ptsStr ++ s!" {c (sx 1)},{c (sy 0)}"
    out := out ++ s!"<polygon points=\\"{areaStr}\\" fill=\\"#0d9488\\" fill-opacity=\\"0.10\\"/>\\n"
    out := out ++ s!"<polyline points=\\"{ptsStr}\\" fill=\\"none\\" stroke=\\"#0d9488\\" stroke-width=\\"2.5\\"/>\\n"
  out := out ++ s!"<rect x=\\"{c L}\\" y=\\"{c T}\\" width=\\"{c size}\\" height=\\"{c size}\\" fill=\\"none\\" stroke=\\"#9fb0b9\\"/>\\n"
  out := out ++ s!"<text x=\\"{c (L + 18)}\\" y=\\"{c (T + 26)}\\" font-size=\\"13\\" font-weight=\\"600\\" fill=\\"#0f766e\\">ROC AUC = {fixed aucVal 3}</text>\\n"
  out := out ++ s!"<text x=\\"{c (L + size / 2)}\\" y=\\"{c (H - 18)}\\" font-size=\\"14\\" text-anchor=\\"middle\\" fill=\\"#172026\\">False Positive Rate (FPR)</text>\\n"
  out := out ++ s!"<text transform=\\"translate(22 {c (T + size / 2)}) rotate(-90)\\" font-size=\\"14\\" text-anchor=\\"middle\\" fill=\\"#172026\\">True Positive Rate (TPR)</text>\\n"
  return out ++ "</svg>\\n"

structure MolSnap where
  canon : String
  bits : List ℕ
  totalH : ℕ
  symClasses : ℕ
  svgStr : String
  molBlk : String
  coordsJson : Array Json
  atomsJson : Array Json
  bondsJson : Array Json
  matJson : Array Json

def buildMolSnap (M : Mol) : MolSnap :=
  let inRing := M.mol.inRingVector
  let B := M.mol.toBondMatrix
  let canon := M.canonicalSmiles
  let bits := M.morganBits
  let totalH := ((List.finRange M.n).map fun i => (M.mol.atom i).totalH).sum
  let dg := Depict.Graph.ofMol M
  let pos := Depict.layout dg
  let svgStr := (Depict.svgWith dg pos 36).render
  let molBlk := Depict.molBlockWith dg pos
  let initRanks := M.mol.toMolData.initialRanks
  let symClasses := numClasses initRanks
  let canonRanks := M.mol.canonicalRanks
  let canonPerm := M.mol.canonicalPerm
  let coordsJson : Array Json := pos.map fun (p : Float × Float) =>
    Json.mkObj [("x", toJson p.1), ("y", toJson p.2)]
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
      ("inRing", toJson inRing[i]),
      ("symmetryRank", toJson initRanks[i]),
      ("canonicalRank", toJson canonRanks[i]),
      ("canonicalIdx", toJson (canonPerm i).val)
    ]
  let bondsJson : Array Json := M.mol.bonds.toArray.map fun (b : Bond M.n) =>
    Json.mkObj [
      ("src", toJson b.src.val),
      ("dst", toJson b.dst.val),
      ("kind", toJson (bondKindName b.kind))
    ]
  let matJson : Array Json := (List.finRange M.n).toArray.map fun i =>
    toJson ((List.finRange M.n).toArray.map fun j => ratStr (B i j))
  { canon, bits, totalH, symClasses, svgStr, molBlk, coordsJson, atomsJson, bondsJson, matJson }

def runParse (s : String) : IO Unit := do
  match tokenize s, parse s with
  | .ok toks, .ok M =>
    let snap := buildMolSnap M
    let toksJson : Array Json := toks.map fun (t : Token) =>
      Json.mkObj [("pos", toJson t.pos), ("show", toJson (tokenLabel t))]
    let (chargeStatus, chargeLog) := match M.checkCharges with
      | .ok () => (Json.mkObj [("ok", toJson true)], "Except.ok ()")
      | .error msg => (Json.mkObj [("ok", toJson false), ("message", toJson msg)], s!"Except.error \\"{msg}\\"")
    let (aromStatus, aromLog) := match M.aromatize with
      | .ok MA =>
        let snapA := buildMolSnap MA
        let toksJsonA : Array Json := match tokenize snapA.canon with
          | .ok ts => ts.map fun (t : Token) => Json.mkObj [("pos", toJson t.pos), ("show", toJson (tokenLabel t))]
          | .error _ => toksJson
        (Json.mkObj [
          ("ok", toJson true),
          ("canonicalSmiles", toJson snapA.canon),
          ("isNormal", toJson MA.isNormal),
          ("symmetryClasses", toJson snapA.symClasses),
          ("totalHydrogens", toJson snapA.totalH),
          ("svg", toJson snapA.svgStr),
          ("molBlock", toJson snapA.molBlk),
          ("coordinates", toJson snapA.coordsJson),
          ("atoms", toJson snapA.atomsJson),
          ("bonds", toJson snapA.bondsJson),
          ("adjMatrix", toJson snapA.matJson),
          ("tokens", toJson toksJsonA),
          ("morganBits", toJson snapA.bits)
        ], s!"Except.ok \\"{snapA.canon}\\"")
      | .error msg =>
        (Json.mkObj [("ok", toJson false), ("message", toJson msg)], s!"Except.error \\"{msg}\\"")
    let logs : Array String := #[
      s!"tokenize \\"{s}\\" --> Except.ok ({toks.size} tokens)",
      s!"parse \\"{s}\\" --> Except.ok (Molecule {M.n} : {M.n} atoms, {M.mol.numBonds} bonds, {snap.totalH} H)",
      s!"numClasses M.mol.toMolData.initialRanks --> {snap.symClasses} symmetry classes",
      s!"(Mol.ofSmiles! \\"{s}\\").canonicalSmiles --> \\"{snap.canon}\\"",
      s!"(Depict.svgWith dg pos 36).render --> 2D SVG ({snap.svgStr.length} chars) + V2000 MolBlock",
      s!"M.checkCharges --> {chargeLog}",
      s!"M.aromatize --> {aromLog}",
      s!"M.morganBits 2 --> {snap.bits} ({snap.bits.length} on-bits)"
    ]
    let out := Json.mkObj [
      ("ok", toJson true),
      ("smiles", toJson s),
      ("canonicalSmiles", toJson snap.canon),
      ("svg", toJson snap.svgStr),
      ("molBlock", toJson snap.molBlk),
      ("coordinates", toJson snap.coordsJson),
      ("n", toJson M.n),
      ("numBonds", toJson M.mol.numBonds),
      ("totalHydrogens", toJson snap.totalH),
      ("isNormal", toJson M.isNormal),
      ("symmetryClasses", toJson snap.symClasses),
      ("chargeCheck", chargeStatus),
      ("aromatized", aromStatus),
      ("tokens", toJson toksJson),
      ("atoms", toJson snap.atomsJson),
      ("bonds", toJson snap.bondsJson),
      ("adjMatrix", toJson snap.matJson),
      ("morganBits", toJson snap.bits),
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
    let path := "datasets/EGFR-FDA.csv"
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
    let path := "datasets/Chembl_EGFR_actives_ML.csv"
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
    let path := "datasets/ThermoPropertiesSMILES.csv"
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

structure FitSample where
  name : String
  smiles : String
  mol : Mol
  bits : Array ℕ
  yFloat : Float
  yRat : ℚ
  isTest : Bool

instance : Inhabited FitSample := ⟨⟨"", "", Mol.empty, #[], 0.0, 0, false⟩⟩

def loadSamplesCached (cacheRef : IO.Ref (List (String × Array FitSample × Array String))) (tsvPath : String) :
    IO (Array FitSample × Array String) := do
  let cache ← cacheRef.get
  match cache.find? (·.1 == tsvPath) with
  | some (_, s, sk) => return (s, sk)
  | none =>
    let raw ← IO.FS.readFile tsvPath
    let lines := (raw.splitOn "\\n").map (fun l => (l.dropEndWhile (· == '\\r')).toString) |>.filter (fun l => !l.trimAscii.isEmpty)
    let mut samples : Array FitSample := #[]
    let mut skipped : Array String := #[]
    for (line, idx) in lines.zipIdx do
      let parts := line.splitOn "\\t"
      match parts with
      | name :: smi :: yStr :: rest =>
        let sp := (rest.head?.getD "").trimAscii.toString
        let isTest := if sp == "test" then true else if sp == "train" then false else (idx % 5 == 0)
        match parse smi.trimAscii.toString, parseSigned? yStr with
        | .ok M, some yf =>
          let MA := match M.aromatize with | .ok mA => mA | .error _ => M
          let bits := (MA.morganBits 2 2048).toArray
          samples := samples.push {
            name := name.trimAscii.toString,
            smiles := smi.trimAscii.toString,
            mol := M,
            bits := bits,
            yFloat := yf,
            yRat := parseRat yStr,
            isTest := isTest
          }
        | .error e, _ => skipped := skipped.push s!"{name}: {e}"
        | _, none => skipped := skipped.push s!"{name}: invalid numeric target '{yStr}'"
      | _ => pure ()
    cacheRef.modify fun c => (tsvPath, samples, skipped) :: c.take 8
    return (samples, skipped)

def runFit (cacheRef : IO.Ref (List (String × Array FitSample × Array String))) (tsvPath modelType alphaStr targetLabel : String) : IO Unit := do
  let (samples, skipped) ← loadSamplesCached cacheRef tsvPath
  if samples.size < 4 then
    let out := Json.mkObj [
      ("ok", toJson false),
      ("error", toJson s!"Need at least 4 valid (SMILES, target) rows; parsed {samples.size} rows.")
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"
    return ()

  let trainSamples := samples.filter (!·.isTest)
  let testSamples := if (samples.filter (·.isTest)).isEmpty then samples.extract 0 (max 1 (samples.size / 5)) else samples.filter (·.isTest)
  let alphaFloat := (parseSigned? alphaStr).getD 1.0
  let alphaRat := parseRat alphaStr

  if modelType == "logistic" then
    let ys := samples.map (·.yFloat)
    let isZeroOne := ys.all (fun y => y == 0.0 || y == 1.0)
    let sortedY := ys.toList.mergeSort (· ≤ ·)
    let threshold := if isZeroOne then 0.5 else sortedY.getD (sortedY.length / 2) 0.0
    let trainData : Array (SparseBits × Bool) := trainSamples.map fun s => (s.bits, s.yFloat > threshold)
    let testData : Array (SparseBits × Bool) := testSamples.map fun s => (s.bits, s.yFloat > threshold)
    let cVal := if alphaFloat > 0.0 then 1.0 / alphaFloat else 1.0
    let cfg : LogisticConfig Float := { C := cVal, maxIter := 500, tol := 0.0001 }
    let (model, iters) := fitLogistic cfg 2048 trainData
    let trainAcc := accuracy model trainData
    let testAcc := accuracy model testData
    let cm := confusionMatrix model testData
    let tn := (cm.getD 0 []).getD 0 0
    let fp := (cm.getD 0 []).getD 1 0
    let fn := (cm.getD 1 []).getD 0 0
    let tp := (cm.getD 1 []).getD 1 0
    let prec : Float := if tp + fp == 0 then 0.0 else tp.toFloat / (tp + fp).toFloat
    let recVal : Float := if tp + fn == 0 then 0.0 else tp.toFloat / (tp + fn).toFloat
    let f1Val : Float := if prec + recVal == 0.0 then 0.0 else 2.0 * prec * recVal / (prec + recVal)
    let testScores : Array (Float × Bool) := testSamples.map fun s => (model.proba s.bits, s.yFloat > threshold)
    let curve := rocCurve testScores
    let aucVal := auc curve
    let svg := rocSvg
      s!"Logistic Classification ROC Curve (C = {fixed cVal 2})"
      s!"LeanSMILES + LeanLearn: Nesterov AGD ({iters} steps) on 2048 Morgan bits"
      curve aucVal
    let topWeights := ((List.range 2048).map fun j => (j, model.weights.getD j 0.0)).mergeSort
      (fun a b => a.2.abs ≥ b.2.abs) |>.take 6
    let topJson : Array Json := topWeights.toArray.map fun (bit, w) =>
      Json.mkObj [("feature", toJson s!"Bit #{bit}"), ("weight", toJson w)]
    let predsJson : Array Json := (samples.take 20).map fun s =>
      let prob := model.proba s.bits
      let actual := if s.yFloat > threshold then 1 else 0
      let pred := if prob >= 0.5 then 1 else 0
      Json.mkObj [
        ("name", toJson s.name),
        ("smiles", toJson s.smiles),
        ("split", toJson (if s.isTest then "test" else "train")),
        ("actual", toJson actual),
        ("predicted", toJson prob),
        ("correct", toJson (actual == pred))
      ]
    let logs : Array String := #[
      s!"morganFeatures (×{samples.size}) --> {trainSamples.size} train, {testSamples.size} test (skipped {skipped.size})",
      s!"fitLogistic (C = {fixed cVal 2}) 2048 train --> converged in {iters} Nesterov steps",
      s!"accuracy model test --> {fixed testAcc 3} (train: {fixed trainAcc 3})",
      s!"rocAuc testScores --> {fixed aucVal 3} · F1 {fixed f1Val 3} · confusion [[{tn}, {fp}], [{fn}, {tp}]]"
    ]
    let out := Json.mkObj [
      ("ok", toJson true),
      ("taskType", toJson "classification"),
      ("modelType", toJson modelType),
      ("trainCount", toJson trainSamples.size),
      ("testCount", toJson testSamples.size),
      ("skippedCount", toJson skipped.size),
      ("iterations", toJson iters),
      ("svg", toJson svg),
      ("metrics", Json.mkObj [
        ("trainAccuracy", toJson trainAcc),
        ("testAccuracy", toJson testAcc),
        ("precision", toJson prec),
        ("recall", toJson recVal),
        ("f1", toJson f1Val),
        ("rocAuc", toJson aucVal),
        ("confusionMatrix", toJson #[(#[tn, fp] : Array ℕ), #[fn, tp]])
      ]),
      ("topFeatures", toJson topJson),
      ("predictions", toJson predsJson),
      ("logs", toJson logs)
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"
  else if modelType == "dense-qr" then
    let featOf (M : Mol) : Array Float :=
      let c := (Representation.counts M).toArray.map Rat.toFloat
      #[1.0] ++ c
    let XTrain : RidgeFloat.Design := trainSamples.map (featOf ·.mol)
    let yTrain : Array Float := trainSamples.map (·.yFloat)
    let pen := if alphaFloat <= 0.0 then 0.0001 else alphaFloat
    let qrCfg : RidgeFloat.Config := { penalty := pen, unpenalizedColumn := some 0 }
    match RidgeFloat.fit XTrain yTrain qrCfg with
    | .ok model =>
      let predictMol (M : Mol) : Float :=
        let row := featOf M
        (List.range row.size).foldl (fun s j => s + row.getD j 0.0 * model.coefficients.getD j 0.0) 0.0
      let trainPairs : Array (Float × Float) := trainSamples.map fun s => (s.yFloat, predictMol s.mol)
      let testPairs : Array (Float × Float) := testSamples.map fun s => (s.yFloat, predictMol s.mol)
      let trR2 := r2 trainPairs
      let trRmse := rmse trainPairs
      let trMae := mae trainPairs
      let teR2 := r2 testPairs
      let teRmse := rmse testPairs
      let teMae := mae testPairs
      let svg := paritySvg
        s!"Householder-QR Ridge Regression (λ = {fixed pen 2})"
        "LeanLearn.Regression.RidgeFloat on Representation.counts (atoms, bonds, H, aromatic, hetero)"
        targetLabel
        [
          { label := "Training", points := trainPairs, r2 := trR2, rmse := trRmse, mae := trMae, filled := false },
          { label := "Test", points := testPairs, r2 := teR2, rmse := teRmse, mae := teMae, filled := true }
        ]
      let names := #["Intercept", "Heavy Atoms (n)", "Bonds", "Total H", "Aromatic Atoms", "Heteroatoms"]
      let topJson : Array Json := (List.range names.size).toArray.map fun j =>
        Json.mkObj [("feature", toJson (names.getD j "")), ("weight", toJson (model.coefficients.getD j 0.0))]
      let predsJson : Array Json := (samples.take 20).map fun s =>
        Json.mkObj [
          ("name", toJson s.name),
          ("smiles", toJson s.smiles),
          ("split", toJson (if s.isTest then "test" else "train")),
          ("actual", toJson s.yFloat),
          ("predicted", toJson (predictMol s.mol))
        ]
      let logs : Array String := #[
        s!"Representation.counts (×{samples.size}) --> 5 exact descriptors + intercept",
        s!"RidgeFloat.fit XTrain yTrain (penalty = {fixed pen 2}) --> Householder QR solved",
        s!"train metrics --> R² {fixed trR2 3}, RMSE {fixed trRmse 3}, MAE {fixed trMae 3}",
        s!"test metrics  --> R² {fixed teR2 3}, RMSE {fixed teRmse 3}, MAE {fixed teMae 3}"
      ]
      let out := Json.mkObj [
        ("ok", toJson true),
        ("taskType", toJson "regression"),
        ("modelType", toJson modelType),
        ("trainCount", toJson trainSamples.size),
        ("testCount", toJson testSamples.size),
        ("skippedCount", toJson skipped.size),
        ("iterations", toJson 6),
        ("svg", toJson svg),
        ("metrics", Json.mkObj [
          ("trainR2", toJson trR2),
          ("trainRmse", toJson trRmse),
          ("trainMae", toJson trMae),
          ("testR2", toJson teR2),
          ("testRmse", toJson teRmse),
          ("testMae", toJson teMae)
        ]),
        ("topFeatures", toJson topJson),
        ("predictions", toJson predsJson),
        ("logs", toJson logs)
      ]
      IO.println s!"__JSON_START__{out.compress}__JSON_END__"
    | .error e =>
      let out := Json.mkObj [("ok", toJson false), ("error", toJson (toString e))]
      IO.println s!"__JSON_START__{out.compress}__JSON_END__"
  else if modelType == "gauss-seidel" || modelType == "jacobi" || modelType == "gradient-descent" then
    let m := trainSamples.size
    let molVec : Vector Mol m := Vector.ofFn fun i => trainSamples[i.val]!.mol
    let yVec : Vector ℚ m := Vector.ofFn fun i => trainSamples[i.val]!.yRat
    let labelled : LabelledMolecules m := { molecules := molVec, targets := yVec }
    let rep : Representation 9 := Representation.bondOrders 3
    let r2Bound : ℚ := 144
    let ridgeVal : ℚ := if alphaRat <= 0 then 1 else alphaRat
    let stepRat : ℚ := 1 / (2 * (r2Bound + 1 + ridgeVal))
    let alg : Algorithm :=
      if modelType == "jacobi" then .jacobi 30
      else if modelType == "gradient-descent" then .gradientDescent stepRat 800
      else .gaussSeidel 30
    let pipe : Pipeline m 9 := { data := labelled, representation := rep, ridge := ridgeVal, algorithm := alg }
    let W := pipe.suggestWitness
    let rhoFloat := W.ratio.toFloat
    let certExcessOpt := pipe.certifiedSolverExcess
    let gdTol := pipe.gdTolerance 4
    let gdCheck := pipe.checkGD r2Bound 4 (gdTol + 1 / 1000)
    let isCertified :=
      if modelType == "gradient-descent" then gdCheck
      else certExcessOpt.isSome
    let certSummary :=
      if modelType == "gradient-descent" then
        s!"checkGD (R²={r2Bound}, η={ratStr stepRat}) = {gdCheck} · tolerance ε = {fixed gdTol.toFloat 4}"
      else
        match certExcessOpt with
        | some e => s!"checkSolver = true (ρ = {fixed rhoFloat 3} < 1, excess ≤ {fixed e.toFloat 6})"
        | none => s!"uncertified (diagonal dominance ratio ρ = {fixed rhoFloat 2} ≥ 1; increase ridge λ)"
    let θ : Vec Float 10 := pipe.model Float
    let trainPairs : Array (Float × Float) := trainSamples.map fun s => (s.yFloat, pipe.predictWith θ s.mol)
    let testPairs : Array (Float × Float) := testSamples.map fun s => (s.yFloat, pipe.predictWith θ s.mol)
    let trR2 := r2 trainPairs
    let trRmse := rmse trainPairs
    let trMae := mae trainPairs
    let teR2 := r2 testPairs
    let teRmse := rmse testPairs
    let teMae := mae testPairs
    let svg := paritySvg
      s!"Certified Pipeline ({modelType}, λ = {fixed ridgeVal.toFloat 1})"
      s!"Pipelines.Pipeline on canonical bondOrders 3 · {certSummary}"
      targetLabel
      [
        { label := "Training", points := trainPairs, r2 := trR2, rmse := trRmse, mae := trMae, filled := false },
        { label := "Test", points := testPairs, r2 := teR2, rmse := teRmse, mae := teMae, filled := true }
      ]
    let predsJson : Array Json := (samples.take 20).map fun s =>
      Json.mkObj [
        ("name", toJson s.name),
        ("smiles", toJson s.smiles),
        ("split", toJson (if s.isTest then "test" else "train")),
        ("actual", toJson s.yFloat),
        ("predicted", toJson (pipe.predictWith θ s.mol))
      ]
    let logs : Array String := #[
      s!"Pipeline.exactProblem ({m} molecules, Representation.bondOrders 3) --> 10×10 normal equations over ℚ",
      s!"pipe.suggestWitness.ratio --> ρ = {fixed rhoFloat 4} ({certSummary})",
      s!"pipe.model Float ({modelType}) --> train R² {fixed trR2 3}, test R² {fixed teR2 3}",
      s!"paritySvg --> generated SVG parity plot"
    ]
    let out := Json.mkObj [
      ("ok", toJson true),
      ("taskType", toJson "regression"),
      ("modelType", toJson modelType),
      ("trainCount", toJson trainSamples.size),
      ("testCount", toJson testSamples.size),
      ("skippedCount", toJson skipped.size),
      ("iterations", toJson (if modelType == "gradient-descent" then 1500 else 35)),
      ("svg", toJson svg),
      ("certificate", Json.mkObj [
        ("certified", toJson isCertified),
        ("ratio", toJson rhoFloat),
        ("summary", toJson certSummary)
      ]),
      ("metrics", Json.mkObj [
        ("trainR2", toJson trR2),
        ("trainRmse", toJson trRmse),
        ("trainMae", toJson trMae),
        ("testR2", toJson teR2),
        ("testRmse", toJson teRmse),
        ("testMae", toJson teMae)
      ]),
      ("predictions", toJson predsJson),
      ("logs", toJson logs)
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"
  else
    let trainData : Array (Array ℕ × Float) := trainSamples.map fun s => (s.bits, s.yFloat)
    let pen := if alphaFloat <= 0.0 then 0.01 else alphaFloat
    let srCfg : SparseRidge.Config Float := { alpha := pen, maxIter := 500, tol := 0.00001 }
    let (model, iters) := SparseRidge.fit srCfg 2048 trainData
    let trainPairs : Array (Float × Float) := trainSamples.map fun s => (s.yFloat, model.predict s.bits)
    let testPairs : Array (Float × Float) := testSamples.map fun s => (s.yFloat, model.predict s.bits)
    let trR2 := r2 trainPairs
    let trRmse := rmse trainPairs
    let trMae := mae trainPairs
    let teR2 := r2 testPairs
    let teRmse := rmse testPairs
    let teMae := mae testPairs
    let svg := paritySvg
      s!"Sparse Ridge on Morgan Fingerprints (α = {fixed pen 2})"
      s!"LeanSMILES + LeanLearn: parse, aromatize, Morgan (2048 bits), {iters} CG steps"
      targetLabel
      [
        { label := "Training", points := trainPairs, r2 := trR2, rmse := trRmse, mae := trMae, filled := false },
        { label := "Test", points := testPairs, r2 := teR2, rmse := teRmse, mae := teMae, filled := true }
      ]
    let topWeights := ((List.range 2048).map fun j => (j, model.weights.getD j 0.0)).mergeSort
      (fun a b => a.2.abs ≥ b.2.abs) |>.take 6
    let topJson : Array Json := topWeights.toArray.map fun (bit, w) =>
      Json.mkObj [("feature", toJson s!"Bit #{bit}"), ("weight", toJson w)]
    let predsJson : Array Json := (samples.take 20).map fun s =>
      Json.mkObj [
        ("name", toJson s.name),
        ("smiles", toJson s.smiles),
        ("split", toJson (if s.isTest then "test" else "train")),
        ("actual", toJson s.yFloat),
        ("predicted", toJson (model.predict s.bits))
      ]
    let logs : Array String := #[
      s!"morganFeatures (×{samples.size}) --> {trainSamples.size} train, {testSamples.size} test (skipped {skipped.size})",
      s!"SparseRidge.fit (alpha = {fixed pen 2}) 2048 train --> {iters} conjugate-gradient steps",
      s!"train metrics --> R² {fixed trR2 3}, RMSE {fixed trRmse 3}, MAE {fixed trMae 3}",
      s!"test metrics  --> R² {fixed teR2 3}, RMSE {fixed teRmse 3}, MAE {fixed teMae 3}",
      s!"LeanLearn.Plot.paritySvg --> rendered SVG parity plot"
    ]
    let out := Json.mkObj [
      ("ok", toJson true),
      ("taskType", toJson "regression"),
      ("modelType", toJson "sparse-ridge"),
      ("trainCount", toJson trainSamples.size),
      ("testCount", toJson testSamples.size),
      ("skippedCount", toJson skipped.size),
      ("iterations", toJson iters),
      ("svg", toJson svg),
      ("metrics", Json.mkObj [
        ("trainR2", toJson trR2),
        ("trainRmse", toJson trRmse),
        ("trainMae", toJson trMae),
        ("testR2", toJson teR2),
        ("testRmse", toJson teRmse),
        ("testMae", toJson teMae)
      ]),
      ("topFeatures", toJson topJson),
      ("predictions", toJson predsJson),
      ("logs", toJson logs)
    ]
    IO.println s!"__JSON_START__{out.compress}__JSON_END__"

partial def loop (cacheRef : IO.Ref (List (String × Array FitSample × Array String))) (stdin stdout : IO.FS.Stream) : IO Unit := do
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
  | ["fit", tsvPath, modelType, alphaStr, targetLabel] =>
    runFit cacheRef tsvPath modelType alphaStr targetLabel
    stdout.flush
  | _ =>
    IO.println "__JSON_START__{\\"ok\\":false,\\"error\\":\\"Unknown command\\"}__JSON_END__"
    stdout.flush
  loop cacheRef stdin stdout

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let cacheRef ← IO.mkRef []
  IO.println "__WORKER_READY__"
  stdout.flush
  loop cacheRef stdin stdout
  return 0
`
  },

  parseMolecule(smiles) {
    return `parse\t${cleanCmdField(smiles)}`
  },

  compareTanimoto(smilesA, smilesB) {
    return `tanimoto\t${cleanCmdField(smilesA)}\t${cleanCmdField(smilesB)}`
  },

  loadDataset(datasetId = 'delaney') {
    return `dataset\t${cleanCmdField(datasetId)}`
  },

  fitPipeline(tsvPath, modelType = 'sparse-ridge', alpha = '1.0', targetLabel = 'target') {
    return `fit\t${cleanCmdField(tsvPath)}\t${cleanCmdField(modelType)}\t${cleanCmdField(String(alpha))}\t${cleanCmdField(targetLabel)}`
  },
}
