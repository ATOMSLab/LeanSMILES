import LeanSMILES.SMILES.Canon
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
import Pipelines.Representation
import Pipelines.Pipeline
import Pipelines.Certificates
import Pipelines.Data
import Lean.Data.Json

/-!
# The web API's Lean worker

One long-lived process behind `server/`: it reads one request per line on
stdin (`parse`, `tanimoto`, `dataset`, `fit`, tab-separated) and answers each
with one line `__JSON_START__{...}__JSON_END__`, in order, after announcing
`__WORKER_READY__`. `server/workers/leanWorker.js` spawns it, queues requests
and caches answers. Build it with `lake build worker`; the binary is
`.lake/build/bin/worker`. Compiled, not interpreted: everything the interpreter
page and the Regression page compute runs here as native code.
-/

open LeanSMILES LeanSMILES.SMILES LeanSMILES.Molecule Lean
open LeanLearn LeanLearn.Regression LeanLearn.Plot Pipelines

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

/-- `x` in scientific notation with `digits` decimals in the mantissa: `2.61e-9`. -/
def sci (x : Float) (digits : Nat := 2) : String :=
  if x == 0 || !x.isFinite then s!"{x}" else
    let e := (Float.log10 x.abs).floor
    let mant := x / (10 : Float) ^ e
    let (mant, e) := if mant.abs >= 10 then (mant / 10, e + 1) else (mant, e)
    s!"{fixed mant digits}e{e.toInt64.toInt}"

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
  pos : Array Depict.Pt

/-- Everything the interpreter shows for one molecule. The 2D layout is the
expensive step (hundreds of stress-majorisation sweeps), so a caller that
already has one for the same skeleton passes it in as pos?. -/
def buildMolSnap (M : Mol) (pos? : Option (Array Depict.Pt) := none) : MolSnap :=
  let inRing := M.mol.inRingVector
  let B := M.mol.toBondMatrix
  let canon := M.canonicalSmiles
  let bits := M.morganBits
  let totalH := ((List.finRange M.n).map fun i => (M.mol.atom i).totalH).sum
  let dg := Depict.Graph.ofMol M
  let pos := match pos? with | some p => p | none => Depict.layout dg
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
  { canon, bits, totalH, symClasses, svgStr, molBlk, coordsJson, atomsJson, bondsJson, matJson, pos }

def runParse (s : String) : IO Unit := do
  match tokenize s, parse s with
  | .ok toks, .ok M =>
    let snap := buildMolSnap M
    let toksJson : Array Json := toks.map fun (t : Token) =>
      Json.mkObj [("pos", toJson t.pos), ("show", toJson (tokenLabel t))]
    let (chargeStatus, chargeLog) := match M.checkCharges with
      | .ok () => (Json.mkObj [("ok", toJson true)], "Except.ok ()")
      | .error msg => (Json.mkObj [("ok", toJson false), ("message", toJson msg)], s!"Except.error \"{msg}\"")
    let (aromStatus, aromLog) := match M.aromatize with
      | .ok MA =>
        -- aromatization changes bond kinds, not the skeleton: reuse the layout
        let snapA := buildMolSnap MA (some snap.pos)
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
        ], s!"Except.ok \"{snapA.canon}\"")
      | .error msg =>
        (Json.mkObj [("ok", toJson false), ("message", toJson msg)], s!"Except.error \"{msg}\"")
    let logs : Array String := #[
      s!"tokenize \"{s}\" --> Except.ok ({toks.size} tokens)",
      s!"parse \"{s}\" --> Except.ok (Molecule {M.n} : {M.n} atoms, {M.mol.numBonds} bonds, {snap.totalH} H)",
      s!"numClasses M.mol.toMolData.initialRanks --> {snap.symClasses} symmetry classes",
      s!"(Mol.ofSmiles! \"{s}\").canonicalSmiles --> \"{snap.canon}\"",
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
      s!"parse \"{s}\" --> Except.error ({reprStr e})",
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
      s!"tokenize \"{s}\" --> Except.error ({reprStr e})",
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
      s!"(Mol.ofSmiles! \"{sA}\").morganBits --> {bitsA.length} bits",
      s!"(Mol.ofSmiles! \"{sB}\").morganBits --> {bitsB.length} bits",
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
    let lines := (raw.splitOn "\n").map (fun l => (l.dropEndWhile (· == '\r')).toString) |>.drop 1 |>.filter (fun l => !l.trimAscii.isEmpty)
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
      s!"let records := CSVparser.load \"{path}\" --> {records.size} molecules",
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
  else
    let path := "datasets/ThermoPropertiesSMILES.csv"
    let raw ← IO.FS.readFile path
    let lines := (raw.splitOn "\n").map (fun l => (l.dropEndWhile (· == '\r')).toString) |>.drop 1 |>.filter (fun l => !l.trimAscii.isEmpty)
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
      s!"CSVparser.splitLine \"{path}\" --> {lines.length} fluid compounds",
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
  /-- `mol` aromatized (`mol` itself if that fails): what the fingerprint and the
  certified pipeline's descriptors are read from. -/
  aro : Mol
  bits : Array ℕ
  yFloat : Float
  yRat : ℚ
  isTest : Bool

instance : Inhabited FitSample := ⟨⟨"", "", Mol.empty, Mol.empty, #[], 0.0, 0, false⟩⟩

def loadSamplesCached (cacheRef : IO.Ref (List (String × Array FitSample × Array String))) (tsvPath : String) :
    IO (Array FitSample × Array String) := do
  let cache ← cacheRef.get
  match cache.find? (·.1 == tsvPath) with
  | some (_, s, sk) => return (s, sk)
  | none =>
    let raw ← IO.FS.readFile tsvPath
    let lines := (raw.splitOn "\n").map (fun l => (l.dropEndWhile (· == '\r')).toString) |>.filter (fun l => !l.trimAscii.isEmpty)
    let mut samples : Array FitSample := #[]
    let mut skipped : Array String := #[]
    for (line, idx) in lines.zipIdx do
      let parts := line.splitOn "\t"
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
            aro := MA,
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

  if modelType == "dense-qr" then
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
    let mQ : ℚ := m
    -- The pipeline's exact ℚ problem: the five count descriptors of the aromatized
    -- molecule, each centred on its training mean and divided by its training mean
    -- absolute deviation, and the target centred on its training mean. The ridge
    -- penalises the bias with the weights, so without the centring a boiling point
    -- near 475 K is pulled toward 0 as soon as λ is large enough to certify; and
    -- without the scaling the raw counts (hydrogens run past 40) are never
    -- diagonally dominant. Both are part of the pipeline (its representation and its
    -- data), so the certificate covers exactly the problem that is trained.
    let trainCounts : Array (Vector ℚ 5) := trainSamples.map fun s => Representation.counts s.aro
    let μ : Vector ℚ 5 := Vector.ofFn fun j => (trainCounts.foldl (fun acc v => acc + v[j]) (0 : ℚ)) / mQ
    let σ : Vector ℚ 5 := Vector.ofFn fun j =>
      let sj := (trainCounts.foldl (fun acc v => acc + |v[j] - μ[j]|) (0 : ℚ)) / mQ
      if sj == 0 then 1 else sj
    let rep : Representation 5 := fun M =>
      let c := Representation.counts M
      Vector.ofFn fun j => (c[j] - μ[j]) / σ[j]
    let yBar : ℚ := (trainSamples.foldl (fun acc s => acc + s.yRat) (0 : ℚ)) / mQ
    let molVec : Vector Mol m := Vector.ofFn fun i => trainSamples[i.val]!.aro
    let yVec : Vector ℚ m := Vector.ofFn fun i => trainSamples[i.val]!.yRat - yBar
    let labelled : LabelledMolecules m := { molecules := molVec, targets := yVec }
    let r2Bound : ℚ := 144
    let ridgeVal : ℚ := if alphaRat <= 0 then 1 else alphaRat
    let stepRat : ℚ := 1 / (2 * (r2Bound + 1 + ridgeVal))
    let alg : Algorithm :=
      if modelType == "jacobi" then .jacobi 30
      else if modelType == "gradient-descent" then .gradientDescent stepRat 800
      else .gaussSeidel 30
    let pipe : Pipeline m 5 := { data := labelled, representation := rep, ridge := ridgeVal, algorithm := alg }
    let W := pipe.suggestWitness
    let rhoFloat := W.ratio.toFloat
    let certExcessOpt := pipe.certifiedSolverExcess
    let gdTol := pipe.gdTolerance 4
    let gdCheck := pipe.checkGD r2Bound 4 (gdTol + 1 / 1000)
    -- The a priori witness: checked before training, it says what the solver will do, but
    -- only where the normal equations are diagonally dominant (large λ).
    let witnessOk :=
      if modelType == "gradient-descent" then gdCheck
      else certExcessOpt.isSome
    let witnessSummary :=
      if modelType == "gradient-descent" then
        s!"checkGD (R²={r2Bound}, η={ratStr stepRat}) = {gdCheck} · tolerance ε = {fixed gdTol.toFloat 4}"
      else
        match certExcessOpt with
        | some e => s!"checkSolver = true (ρ = {fixed rhoFloat 3} < 1, excess ≤ {fixed e.toFloat 6})"
        | none => s!"uncertified (diagonal dominance ratio ρ = {fixed rhoFloat 2} ≥ 1; increase ridge λ)"
    let θ : Vec Float 6 := pipe.model Float
    -- The a posteriori certificate: read the trained Float weights exactly and check the
    -- residual of the exact normal equations at them. `Pipeline.checkResidual_sound` then
    -- bounds the excess training loss of exactly these weights, at any λ > 0, whatever the
    -- solver did: the tolerance is one millionth of their own training loss.
    let θQ : Vec ℚ 6 := θ.map ratOfFloatExact
    let lossQ : ℚ := pipe.exactProblem.loss θQ
    let resExcess : ℚ := pipe.residualExcess θQ
    let resTol : ℚ := lossQ / 1000000
    let isCertified := pipe.checkResidual θQ resTol
    let resExcessF := resExcess.toFloat
    let lossF := lossQ.toFloat
    let resShare := if lossF > 0 then resExcessF / lossF else 0
    let certSummary :=
      if isCertified then
        s!"checkResidual = true: ‖Aθ − b‖²/λ = {sci resExcessF} ≤ 10⁻⁶ · L(θ) (L(θ) = {fixed lossF 4})"
      else
        s!"checkResidual = false: ‖Aθ − b‖²/λ = {sci resExcessF} = {sci resShare} · L(θ) (L(θ) = {fixed lossF 4}), above the 10⁻⁶ · L(θ) tolerance — 30 sweeps stopped short of the optimum"
    let certShort :=
      if isCertified then s!"residual certificate: excess loss ≤ {sci resExcessF}"
      else s!"residual bound {sci resExcessF}, above the 10⁻⁶ L(θ) tolerance"
    let yBarF := yBar.toFloat
    let predictMol (s : FitSample) : Float := pipe.predictWith θ s.aro + yBarF
    let trainPairs : Array (Float × Float) := trainSamples.map fun s => (s.yFloat, predictMol s)
    let testPairs : Array (Float × Float) := testSamples.map fun s => (s.yFloat, predictMol s)
    let trR2 := r2 trainPairs
    let trRmse := rmse trainPairs
    let trMae := mae trainPairs
    let teR2 := r2 testPairs
    let teRmse := rmse testPairs
    let teMae := mae testPairs
    let svg := paritySvg
      s!"Certified Pipeline ({modelType}, λ = {fixed ridgeVal.toFloat 1})"
      s!"Pipelines.Pipeline on 5 standardized count descriptors · {certShort}"
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
        ("predicted", toJson (predictMol s))
      ]
    let names := #["Heavy Atoms (n)", "Bonds", "Total H", "Aromatic Atoms", "Heteroatoms"]
    let topJson : Array Json := (List.range names.size).toArray.map fun j =>
      Json.mkObj [("feature", toJson (names.getD j "")), ("weight", toJson (θ.toArray.getD j 0.0))]
    let logs : Array String := #[
      s!"Pipeline.exactProblem ({m} molecules, Representation.counts centred and scaled by mean absolute deviation, target centred on {fixed yBarF 2}) --> 6×6 normal equations over ℚ",
      s!"pipe.suggestWitness (a priori, before training) --> ρ = {fixed rhoFloat 4}: {witnessSummary}",
      s!"pipe.model Float ({modelType}) --> train R² {fixed trR2 3}, test R² {fixed teR2 3}",
      s!"pipe.checkResidual θ (a posteriori, θ read exactly as ℚ, ε = 10⁻⁶ L(θ)) --> {certSummary}",
      s!"paritySvg --> generated SVG parity plot"
    ]
    let out := Json.mkObj [
      ("ok", toJson true),
      ("taskType", toJson "regression"),
      ("modelType", toJson modelType),
      ("trainCount", toJson trainSamples.size),
      ("testCount", toJson testSamples.size),
      ("skippedCount", toJson skipped.size),
      ("iterations", toJson (if modelType == "gradient-descent" then 800 else 30)),
      ("svg", toJson svg),
      ("certificate", Json.mkObj [
        ("certified", toJson isCertified),
        ("summary", toJson certSummary),
        ("residualExcess", toJson resExcessF),
        ("trainLoss", toJson lossF),
        ("tolerance", toJson resTol.toFloat),
        ("witnessOk", toJson witnessOk),
        ("ratio", toJson rhoFloat),
        ("witnessSummary", toJson witnessSummary)
      ]),
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
  let parts := line.trimAscii.toString.splitOn "\t"
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
    IO.println "__JSON_START__{\"ok\":false,\"error\":\"Unknown command\"}__JSON_END__"
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
