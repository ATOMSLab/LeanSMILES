import React, { useState, useEffect, useRef } from 'react'
import { useNavigate } from 'react-router-dom'
import { Upload, Download, CheckCircle2, AlertTriangle, Sparkles } from 'lucide-react'
import api, { newRequestHandle } from '../middleware/api'
import { Card, Badge, Button, SectionHeader, DataTable, BusyBar, SpinnerPill, LogConsole } from '../components/UI'

const DATASET_TABS = [
  {
    id: 'delaney',
    label: 'Delaney ESOL Solubility',
    path: 'datasets/delaney-processed.csv',
    defaultModel: 'sparse-ridge',
    targetLabel: 'log solubility (log mol/L)',
  },
  {
    id: 'thermo',
    label: 'ThermoProperties Boiling Point',
    path: 'datasets/ThermoPropertiesSMILES.csv',
    defaultModel: 'sparse-ridge',
    targetLabel: 'Boiling Point (K)',
  },
]

// Two solvers: the real model (tested against scikit-learn, no theorem) and the
// certified pipeline whose certificate can genuinely fail. Jacobi (exact-ℚ
// certificate runs for minutes at λ ≤ 1), gradient descent (certificate passes
// by construction) and Householder-QR are still served by the API, just not
// offered here.
const MODEL_OPTIONS = [
  { id: 'sparse-ridge', label: 'Sparse Ridge (2048 Morgan Bits)' },
  { id: 'gauss-seidel', label: 'Certified Gauss–Seidel (ℚ Pipeline)' },
]

const MODEL_NOTES = {
  'sparse-ridge': (
    <>
      No theorem behind this one: conjugate gradients on 2048 Morgan bits, checked against scikit-learn's{' '}
      <code className="font-mono">Ridge</code> to 10⁻⁶ by <code className="font-mono">lake exe ridge-test</code>. Tested, not proven.
    </>
  ),
  'gauss-seidel': (
    <>
      <span className="font-medium text-slate-700">Certified</span> means: before training, Lean checks an exact-arithmetic (ℚ)
      witness on this dataset's normal equations — diagonal dominance, ρ &lt; 1 — and the theorem{' '}
      <code className="font-mono">Pipeline.checkSolver_sound</code> proves that whenever that check passes, the solver's
      exact-real iterates land within ε of the optimal training loss. It does not cover the floating-point numbers shown
      (the same code run in Float) or accuracy on the test set. The pipeline fits five count descriptors (heavy atoms,
      bonds, hydrogens, aromatic atoms, heteroatoms), standardized, to the centred target — all in exact ℚ — so expect a
      modest R²: the witness needs λ ≥ 4 on these datasets, and five counts carry less than 2048 Morgan bits. At small λ
      the witness fails, and the page says so.
    </>
  ),
}

const PENALTY_OPTIONS = ['0.1', '1.0', '4.0', '16.0']

function parseUploadedCsv(text) {
  const lines = text
    .split(/\r?\n/)
    .map((l) => l.trim())
    .filter(Boolean)
  if (lines.length < 2) return null

  const splitRow = (row) => {
    const sep = row.includes('\t') && !row.includes(',') ? '\t' : ','
    const out = []
    let cur = ''
    let inQuotes = false
    for (let i = 0; i < row.length; i++) {
      const ch = row[i]
      if (ch === '"') inQuotes = !inQuotes
      else if (ch === sep && !inQuotes) {
        out.push(cur.trim())
        cur = ''
      } else {
        cur += ch
      }
    }
    out.push(cur.trim())
    return out
  }

  const headers = splitRow(lines[0]).map((h, i) => h || `Column_${i + 1}`)
  const rawRows = lines.slice(1).map(splitRow)

  let smilesIdx = headers.findIndex((h) => /smiles|smi|canon/i.test(h))
  if (smilesIdx === -1) {
    smilesIdx = headers.findIndex((_, colIdx) =>
      rawRows.slice(0, 5).some((r) => /[CcNnOo][12=#()CcNnOo]/.test(r[colIdx] || ''))
    )
  }
  if (smilesIdx === -1) smilesIdx = 0

  let targetIdx = headers.findIndex(
    (h, idx) =>
      idx !== smilesIdx &&
      /solubility|logs|target|label|bp|boiling|y|value|score/i.test(h) &&
      !Number.isNaN(Number(rawRows[0]?.[idx]))
  )
  if (targetIdx === -1) {
    targetIdx = headers.findIndex(
      (_, idx) =>
        idx !== smilesIdx &&
        rawRows.slice(0, 5).filter((r) => r[idx] !== undefined && r[idx] !== '' && !Number.isNaN(Number(r[idx]))).length >= 3
    )
  }
  if (targetIdx === -1) targetIdx = Math.min(1, headers.length - 1)

  let nameIdx = headers.findIndex((h, idx) => idx !== smilesIdx && idx !== targetIdx && /name|id|compound|mol/i.test(h))
  if (nameIdx === -1) nameIdx = 0

  return { headers, rawRows, smilesIdx, targetIdx, nameIdx }
}

export default function Datasets() {
  const [datasetId, setDatasetId] = useState('delaney')
  const [query, setQuery] = useState('')
  const [loadingTable, setLoadingTable] = useState(false)
  const [tableState, setTableState] = useState({ rows: [], totalCount: 0, logs: [], leanFeedback: null })

  const [modelType, setModelType] = useState('sparse-ridge')
  const [alpha, setAlpha] = useState('1.0')
  const [fitting, setFitting] = useState(false)
  const [fitResult, setFitResult] = useState(null)
  const [fitError, setFitError] = useState('')

  const [uploadedCsv, setUploadedCsv] = useState(null)
  const [smilesCol, setSmilesCol] = useState(0)
  const [targetCol, setTargetCol] = useState(1)

  const fileInputRef = useRef(null)
  const fitReqId = useRef(0)
  const fitHandle = useRef(null)
  const tableHandle = useRef(null)
  const [busyMeta, setBusyMeta] = useState(null)
  const navigate = useNavigate()

  const buildCustomRows = (csvObj, sIdx, tIdx) => {
    if (!csvObj) return null
    return csvObj.rawRows
      .map((r, i) => ({
        name: r[csvObj.nameIdx] || `Row_${i + 1}`,
        smiles: r[sIdx] || '',
        target: r[tIdx] ?? '',
        canonicalSmiles: r[sIdx] || '',
        atoms: '-',
        bonds: '-',
        metricLabel: csvObj.headers[tIdx] || 'Target',
        metricValue: Number.isNaN(Number(r[tIdx])) ? r[tIdx] : Number(r[tIdx]),
      }))
      .filter((r) => r.smiles && r.target !== '' && !Number.isNaN(Number(r.target)))
  }

  const runPipelineFit = async ({
    dsId = datasetId,
    customRows = null,
    model = modelType,
    pen = alpha,
    label = 'target',
  }) => {
    const reqId = ++fitReqId.current
    // one fit at a time: a new one cancels the previous, on the server too
    fitHandle.current?.cancel()
    const handle = newRequestHandle()
    fitHandle.current = handle
    setBusyMeta({
      label: 'Fitting in Lean 4: featurize, solve, draw the parity plot',
      startedAt: Date.now(),
      expectedMs: 300 + 4 * (customRows ? customRows.length : 205),
    })
    setFitting(true)
    setFitError('')
    try {
      const res = await api.fitPipeline(
        {
          datasetId: dsId,
          customRows,
          modelType: model,
          alpha: pen,
          targetLabel: label,
        },
        handle
      )
      if (reqId !== fitReqId.current) return
      setFitResult(res)
    } catch (err) {
      if (reqId !== fitReqId.current || err.cancelled) return
      setFitError(err.details?.error || err.message || 'Model fitting failed in Lean 4')
    } finally {
      if (reqId === fitReqId.current) {
        setFitting(false)
        fitHandle.current = null
      }
    }
  }

  const selectBuiltinDataset = async (tabObj) => {
    setUploadedCsv(null)
    setDatasetId(tabObj.id)
    setModelType(tabObj.defaultModel)
    setLoadingTable(true)
    tableHandle.current?.cancel()
    const handle = newRequestHandle()
    tableHandle.current = handle
    runPipelineFit({
      dsId: tabObj.id,
      customRows: null,
      model: tabObj.defaultModel,
      pen: alpha,
      label: tabObj.targetLabel,
    })
    try {
      const res = await api.getDatasets(tabObj.id, handle)
      if (tableHandle.current === handle) setTableState(res)
    } catch (err) {
      if (tableHandle.current === handle && !err.cancelled) {
        setFitError(err.details?.error || err.message || 'Could not load the dataset in Lean 4')
      }
    } finally {
      if (tableHandle.current === handle) {
        setLoadingTable(false)
        tableHandle.current = null
      }
    }
  }

  useEffect(() => {
    selectBuiltinDataset(DATASET_TABS[0])
  }, [])

  const handleModelChange = (newModel) => {
    setModelType(newModel)
    const activeTab = DATASET_TABS.find((t) => t.id === datasetId) || DATASET_TABS[0]
    const customRows = uploadedCsv ? buildCustomRows(uploadedCsv, smilesCol, targetCol) : null
    const label = uploadedCsv ? uploadedCsv.headers[targetCol] || 'Target' : activeTab.targetLabel
    runPipelineFit({
      dsId: datasetId,
      customRows,
      model: newModel,
      pen: alpha,
      label,
    })
  }

  const handleAlphaChange = (newAlpha) => {
    setAlpha(newAlpha)
    const activeTab = DATASET_TABS.find((t) => t.id === datasetId) || DATASET_TABS[0]
    const customRows = uploadedCsv ? buildCustomRows(uploadedCsv, smilesCol, targetCol) : null
    const label = uploadedCsv ? uploadedCsv.headers[targetCol] || 'Target' : activeTab.targetLabel
    runPipelineFit({
      dsId: datasetId,
      customRows,
      model: modelType,
      pen: newAlpha,
      label,
    })
  }

  const handleFileUpload = (e) => {
    const file = e.target.files?.[0]
    if (!file) return
    const reader = new FileReader()
    reader.onload = (ev) => {
      const parsed = parseUploadedCsv(String(ev.target?.result || ''))
      if (!parsed || parsed.rawRows.length === 0) {
        setFitError('Could not parse CSV file. Ensure it has a header row, a SMILES column, and a numeric target column.')
        return
      }
      const csvMeta = { ...parsed, fileName: file.name }
      setUploadedCsv(csvMeta)
      setDatasetId('custom')
      setSmilesCol(parsed.smilesIdx)
      setTargetCol(parsed.targetIdx)

      const customRows = buildCustomRows(csvMeta, parsed.smilesIdx, parsed.targetIdx)

      setTableState({
        rows: customRows.slice(0, 50),
        totalCount: customRows.length,
        logs: [`Uploaded "${file.name}" --> ${customRows.length} valid (SMILES, target) rows`],
        leanFeedback: null,
      })

      runPipelineFit({
        dsId: 'custom',
        customRows,
        model: modelType,
        pen: alpha,
        label: parsed.headers[parsed.targetIdx] || 'Target',
      })
    }
    reader.readAsText(file)
  }

  const handleColumnChange = (newSmilesIdx, newTargetIdx) => {
    setSmilesCol(newSmilesIdx)
    setTargetCol(newTargetIdx)
    if (!uploadedCsv) return
    const customRows = buildCustomRows(uploadedCsv, newSmilesIdx, newTargetIdx)
    setTableState((prev) => ({
      ...prev,
      rows: customRows.slice(0, 50),
      totalCount: customRows.length,
    }))
    runPipelineFit({
      dsId: 'custom',
      customRows,
      model: modelType,
      pen: alpha,
      label: uploadedCsv.headers[newTargetIdx] || 'Target',
    })
  }

  const handleDownloadSvg = () => {
    if (!fitResult?.svg) return
    const blob = new Blob([fitResult.svg], { type: 'image/svg+xml' })
    const url = URL.createObjectURL(blob)
    const a = document.createElement('a')
    a.href = url
    a.download = `lean-${datasetId}-${modelType}-parity.svg`
    a.click()
    URL.revokeObjectURL(url)
  }

  const rows = tableState.rows || []
  const filtered = rows.filter(
    (d) =>
      d.name?.toLowerCase().includes(query.toLowerCase()) ||
      d.smiles?.toLowerCase().includes(query.toLowerCase()) ||
      d.canonicalSmiles?.toLowerCase().includes(query.toLowerCase())
  )

  const combinedLogs = [...(fitResult?.logs || []), ...(tableState.logs || [])]

  // Stop whatever Lean is doing for this page: the fit and the dataset parse.
  // Stale answers are ignored by the request ids; the server drops the jobs.
  const cancelBusy = () => {
    fitReqId.current += 1
    fitHandle.current?.cancel()
    fitHandle.current = null
    tableHandle.current?.cancel()
    tableHandle.current = null
    setFitting(false)
    setLoadingTable(false)
    setBusyMeta(null)
  }
  const busy = fitting || loadingTable

  return (
    <div className="space-y-6">
      <SectionHeader
        title="Datasets & Lean Regression Pipeline"
        description="Select a built-in benchmark or upload any CSV with SMILES and a numeric target column, then fit Sparse Ridge on Morgan fingerprints or the certified Gauss–Seidel pipeline in Lean 4."
        right={
          busy && (
            <BusyBar
              label={fitting ? busyMeta?.label || 'Fitting in Lean 4' : 'Parsing the dataset in Lean 4'}
              startedAt={busyMeta?.startedAt}
              expectedMs={busyMeta?.expectedMs}
              onCancel={cancelBusy}
            />
          )
        }
      />

      <Card
        title="1. Dataset Source & Regression Solver"
        subtitle="Upload your own CSV (SMILES + numeric target) or pick a repository dataset"
        action={
          <div>
            <input
              ref={fileInputRef}
              type="file"
              accept=".csv,.tsv,.txt"
              onChange={handleFileUpload}
              className="hidden"
            />
            <Button
              variant="primary"
              disabled={busy}
              onClick={() => fileInputRef.current?.click()}
              className="inline-flex items-center gap-1.5"
            >
              <Upload size={13} />
              {uploadedCsv ? `Uploaded: ${uploadedCsv.fileName}` : 'Upload CSV (SMILES + Target)'}
            </Button>
          </div>
        }
      >
        <div className="space-y-4">
          <div className="flex flex-wrap gap-1.5">
            {DATASET_TABS.map((t) => (
              <button
                key={t.id}
                type="button"
                disabled={busy}
                onClick={() => selectBuiltinDataset(t)}
                className={`px-3 py-1.5 rounded-xl text-xs transition cursor-pointer disabled:opacity-40 disabled:cursor-not-allowed ${
                  datasetId === t.id && !uploadedCsv
                    ? 'bg-slate-900 text-white font-medium'
                    : 'bg-slate-100/80 text-slate-600 hover:bg-slate-200/70'
                }`}
              >
                {t.label}
              </button>
            ))}
          </div>

          {uploadedCsv && (
            <div className="p-3.5 rounded-xl bg-teal-50/50 border border-teal-200/70 flex flex-wrap items-center justify-between gap-4 text-xs">
              <div className="flex items-center gap-2 text-teal-900 font-medium">
                <Sparkles size={14} className="text-teal-600" />
                <span>
                  Custom CSV: <code className="font-mono">{uploadedCsv.fileName}</code> ({tableState.totalCount} valid rows)
                </span>
              </div>
              <div className="flex flex-wrap items-center gap-3">
                <label className="flex items-center gap-1.5 text-slate-600">
                  <span>SMILES Column:</span>
                  <select
                    value={smilesCol}
                    disabled={busy}
                    onChange={(e) => handleColumnChange(Number(e.target.value), targetCol)}
                    className="px-2.5 py-1 rounded-lg bg-white border border-slate-200 text-slate-800 font-mono text-xs"
                  >
                    {uploadedCsv.headers.map((h, i) => (
                      <option key={i} value={i}>
                        {h}
                      </option>
                    ))}
                  </select>
                </label>
                <label className="flex items-center gap-1.5 text-slate-600">
                  <span>Target Label:</span>
                  <select
                    value={targetCol}
                    disabled={busy}
                    onChange={(e) => handleColumnChange(smilesCol, Number(e.target.value))}
                    className="px-2.5 py-1 rounded-lg bg-white border border-slate-200 text-slate-800 font-mono text-xs"
                  >
                    {uploadedCsv.headers.map((h, i) => (
                      <option key={i} value={i}>
                        {h}
                      </option>
                    ))}
                  </select>
                </label>
              </div>
            </div>
          )}

          <div className="pt-3 border-t border-slate-200/60 flex flex-col sm:flex-row sm:items-center justify-between gap-4">
            <div className="space-y-1.5">
              <p className="text-[11px] font-medium text-slate-400 uppercase tracking-wider">
                LeanLearn / Pipelines Regression Model
              </p>
              <div className="flex flex-wrap gap-1.5">
                {MODEL_OPTIONS.map((m) => (
                  <button
                    key={m.id}
                    type="button"
                    disabled={busy}
                    onClick={() => handleModelChange(m.id)}
                    className={`px-2.5 py-1.5 rounded-lg text-xs transition cursor-pointer disabled:opacity-40 disabled:cursor-not-allowed ${
                      modelType === m.id
                        ? 'bg-teal-700 text-white font-medium'
                        : 'bg-slate-100/80 text-slate-600 hover:bg-slate-200/70'
                    }`}
                  >
                    {m.label}
                  </button>
                ))}
              </div>
              {MODEL_NOTES[modelType] && (
                <p className="text-[11px] leading-relaxed text-slate-500 max-w-xl pt-1">{MODEL_NOTES[modelType]}</p>
              )}
            </div>

            <div className="space-y-1.5 shrink-0">
              <p className="text-[11px] font-medium text-slate-400 uppercase tracking-wider">
                Penalty (α / λ)
              </p>
              <div className="flex items-center gap-1">
                {PENALTY_OPTIONS.map((p) => (
                  <button
                    key={p}
                    type="button"
                    disabled={busy}
                    onClick={() => handleAlphaChange(p)}
                    className={`px-2.5 py-1.5 rounded-lg font-mono text-xs transition cursor-pointer disabled:opacity-40 disabled:cursor-not-allowed ${
                      alpha === p
                        ? 'bg-slate-900 text-white font-medium'
                        : 'bg-slate-100/80 text-slate-600 hover:bg-slate-200/70'
                    }`}
                  >
                    {p}
                  </button>
                ))}
              </div>
            </div>
          </div>

          {fitError && (
            <div className="p-3 rounded-xl bg-rose-50 border border-rose-200/70 text-xs text-rose-800 font-mono">
              {fitError}
            </div>
          )}
        </div>
      </Card>

      {fitResult && (
        <div className={`grid md:grid-cols-12 gap-6 transition-opacity duration-150 ${fitting ? 'opacity-55' : 'opacity-100'}`}>
          <Card
            className="md:col-span-6"
            title="Lean Parity Plot SVG (LeanLearn.Plot.paritySvg)"
            subtitle={`${fitResult.trainCount} train · ${fitResult.testCount} test molecules · ${fitResult.iterations} solver steps`}
            action={
              <Button
                variant="secondary"
                onClick={handleDownloadSvg}
                className="!px-2.5 !py-1 inline-flex items-center gap-1"
              >
                <Download size={12} /> .svg
              </Button>
            }
          >
            <div
              className="w-full rounded-xl bg-white border border-slate-200/70 p-2 flex items-center justify-center overflow-hidden [&>svg]:w-full [&>svg]:h-auto [&>svg]:max-h-[405px]"
              dangerouslySetInnerHTML={{ __html: fitResult.svg }}
            />
          </Card>

          <Card
            className="md:col-span-6"
            title="Error Metrics, Certificates & Predictions"
            subtitle="Evaluated by LeanLearn.Regression.Metrics (r2, rmse, mae)"
            action={<Badge active>Regression</Badge>}
          >
            <div className="space-y-4">
              {fitResult.certificate && (
                <div
                  className={`p-3 rounded-xl border flex items-start gap-2.5 text-xs ${
                    fitResult.certificate.certified
                      ? 'bg-teal-50/60 border-teal-200/80 text-teal-900'
                      : 'bg-amber-50/60 border-amber-200/80 text-amber-900'
                  }`}
                >
                  {fitResult.certificate.certified ? (
                    <CheckCircle2 size={15} className="text-teal-600 mt-0.5 shrink-0" />
                  ) : (
                    <AlertTriangle size={15} className="text-amber-600 mt-0.5 shrink-0" />
                  )}
                  <div>
                    <div className="font-semibold">
                      {fitResult.certificate.certified
                        ? 'Certificate checked: exact-ℚ witness passed (ρ < 1)'
                        : 'Certificate not met at this λ (ρ ≥ 1) — try a larger λ'}
                    </div>
                    <p className="font-mono text-[11px] mt-0.5 opacity-85">
                      {fitResult.certificate.summary}
                    </p>
                  </div>
                </div>
              )}

              <div className="grid grid-cols-3 gap-2.5">
                <div className="p-3 rounded-xl bg-slate-900/[0.02] border border-slate-200/70">
                  <p className="text-[11px] text-slate-400">Test R²</p>
                  <p className="text-lg font-semibold font-mono text-slate-900 mt-0.5">
                    {Number(fitResult.metrics?.testR2 ?? 0).toFixed(3)}
                  </p>
                  <p className="text-[10px] font-mono text-slate-400">
                    Train: {Number(fitResult.metrics?.trainR2 ?? 0).toFixed(3)}
                  </p>
                </div>
                <div className="p-3 rounded-xl bg-slate-900/[0.02] border border-slate-200/70">
                  <p className="text-[11px] text-slate-400">Test RMSE</p>
                  <p className="text-lg font-semibold font-mono text-teal-700 mt-0.5">
                    {Number(fitResult.metrics?.testRmse ?? 0).toFixed(3)}
                  </p>
                  <p className="text-[10px] font-mono text-slate-400">
                    Train: {Number(fitResult.metrics?.trainRmse ?? 0).toFixed(3)}
                  </p>
                </div>
                <div className="p-3 rounded-xl bg-slate-900/[0.02] border border-slate-200/70">
                  <p className="text-[11px] text-slate-400">Test MAE</p>
                  <p className="text-lg font-semibold font-mono text-slate-900 mt-0.5">
                    {Number(fitResult.metrics?.testMae ?? 0).toFixed(3)}
                  </p>
                  <p className="text-[10px] font-mono text-slate-400">
                    Train: {Number(fitResult.metrics?.trainMae ?? 0).toFixed(3)}
                  </p>
                </div>
              </div>

              <div>
                <p className="text-[11px] text-slate-400 mb-1.5">Sample Model Predictions</p>
                <DataTable
                  maxHeight="max-h-52"
                  columns={[
                    { key: 'name', label: 'Compound', render: (v) => <span className="font-medium text-slate-800">{v}</span> },
                    {
                      key: 'split',
                      label: 'Split',
                      render: (v) => <Badge active={v === 'test'}>{v}</Badge>,
                    },
                    {
                      key: 'actual',
                      label: 'Measured',
                      render: (v) => <code className="font-mono text-slate-600">{typeof v === 'number' ? Number(v.toFixed(2)) : v}</code>,
                    },
                    {
                      key: 'predicted',
                      label: 'Predicted',
                      render: (v) => (
                        <code className="font-mono text-teal-700 font-semibold">
                          {typeof v === 'number' ? Number(v.toFixed(3)) : v}
                        </code>
                      ),
                    },
                  ]}
                  rows={fitResult.predictions || []}
                />
              </div>
            </div>
          </Card>
        </div>
      )}

      <Card
        title="2. Dataset Rows Explorer (CSVparser.lean)"
        subtitle={
          tableState.totalCount
            ? `${tableState.totalCount} total rows · Click Interpret to inspect any molecule in SMILES Interpreter`
            : 'Select or upload a dataset'
        }
        action={
          <div className="flex items-center gap-2">
            {loadingTable && <SpinnerPill label="Loading..." />}
            <input
              value={query}
              onChange={(e) => setQuery(e.target.value)}
              placeholder="Filter rows..."
              className="px-3 py-1.5 rounded-xl bg-slate-900/[0.02] border border-slate-200/80 text-xs focus:outline-none"
            />
          </div>
        }
      >
        <div className={`transition-opacity duration-150 ${loadingTable ? 'opacity-55' : 'opacity-100'}`}>
          <DataTable
            maxHeight="max-h-96"
            columns={[
              { key: 'name', label: 'Compound / ID', render: (v) => <span className="font-medium text-slate-800">{v}</span> },
              { key: 'smiles', label: 'Input SMILES', render: (v) => <code className="font-mono text-slate-500">{v}</code> },
              {
                key: 'canonicalSmiles',
                label: 'Lean Canonical SMILES',
                render: (v) => <code className="font-mono text-teal-700">{v}</code>,
              },
              {
                key: 'atoms',
                label: 'Molecule n',
                render: (_, r) => (
                  <span className="font-mono text-slate-600 whitespace-nowrap">
                    {r.atoms} atoms · {r.bonds} bonds
                  </span>
                ),
              },
              {
                key: 'metricValue',
                label: rows[0]?.metricLabel || 'Target',
                render: (v) => <Badge active>{typeof v === 'number' ? Number(v.toFixed(3)) : v}</Badge>,
              },
              {
                key: 'action',
                label: '',
                render: (_, row) => (
                  <Button
                    variant="secondary"
                    onClick={() => navigate(`/lab?smiles=${encodeURIComponent(row.smiles)}`)}
                    className="!px-2.5 !py-1"
                  >
                    Interpret
                  </Button>
                ),
              },
            ]}
            rows={filtered}
          />
        </div>
      </Card>

      <LogConsole
        logs={combinedLogs}
        feedback={fitResult?.leanFeedback || tableState.leanFeedback}
        loading={fitting || loadingTable}
      />
    </div>
  )
}
