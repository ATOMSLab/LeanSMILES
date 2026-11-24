import React, { useState, useEffect, useRef } from 'react'
import { useSearchParams } from 'react-router-dom'
import { Plus, X, Download, Copy, Check } from 'lucide-react'
import api, { PRESET_MOLECULES, newRequestHandle } from '../middleware/api'
import {
  Card,
  Badge,
  Button,
  SectionHeader,
  DataTable,
  BusyBar,
  LogConsole,
} from '../components/UI'
import MoleculeGraph from '../components/MoleculeGraph'

const COMPARE_PRESETS = [
  { label: 'Theobromine', smiles: 'Cn1cnc2c1c(=O)[nH]c(=O)n2C' },
  { label: 'Propanol', smiles: 'CCCO' },
  { label: 'Ethanol (OCC)', smiles: 'OCC' },
]

function buildDiagnostics(data, errorInfo) {
  if (errorInfo) {
    return {
      status: 'error',
      items: [
        {
          type: 'error',
          label: errorInfo.isServiceError
            ? 'Lean Server Unavailable'
            : errorInfo.isGrammarDeviation
              ? 'OpenSMILES §2.2 Rule'
              : 'SMILES Syntax Error',
          tag: errorInfo.constructor || 'ParseError',
          detail: errorInfo.error,
        },
        ...(errorInfo.explanation
          ? [
              {
                type: 'warn',
                label: errorInfo.isServiceError ? 'What Happened' : 'How to Fix',
                tag: 'LeanSMILES.SMILES.Parse',
                detail: errorInfo.explanation,
              },
            ]
          : []),
      ],
    }
  }
  if (!data) return null

  const chargeOk = data.chargeCheck?.ok !== false
  const aromOk = data.aromatized?.ok !== false
  return {
    status: !chargeOk || !aromOk ? 'warn' : 'ok',
    items: [
      {
        type: 'ok',
        label: 'OpenSMILES Syntax',
        tag: `Molecule ${data.n}`,
        detail: `Parsed ${data.tokens.length} tokens into ${data.n} atoms and ${data.numBonds} bonds (${data.symmetryClasses || data.n} symmetry classes).`,
      },
      {
        type: chargeOk ? 'ok' : 'warn',
        label: 'Formal Charge Check',
        tag: 'Mol.checkCharges',
        detail: chargeOk
          ? 'All atoms within physical noble-gas shell bounds (-shellVacancy ≤ charge ≤ Z).'
          : data.chargeCheck.message,
      },
      {
        type: aromOk ? 'ok' : 'warn',
        label: 'RDKit cleanUp & Hückel 4n+2',
        tag: 'Mol.aromatize',
        detail: aromOk
          ? `Canonical sanitized: ${data.aromatized?.canonicalSmiles}`
          : data.aromatized?.message,
      },
    ],
  }
}

const ATOM_COLUMNS = [
  { key: 'idx', label: 'Fin n', render: (v) => <code className="text-slate-400">{v}</code> },
  { key: 'raw', label: 'Token', render: (v) => <code className="font-mono text-slate-800">{v}</code> },
  { key: 'symbol', label: 'Element' },
  { key: 'degree', label: 'Degree' },
  { key: 'totalH', label: 'Hydrogens' },
  { key: 'charge', label: 'Charge', render: (v) => <code className="font-mono">{v > 0 ? `+${v}` : v}</code> },
  { key: 'symmetryRank', label: 'Symmetry', render: (v) => <Badge>Class {v}</Badge> },
  { key: 'inRing', label: 'Topology', render: (v) => <Badge active={v}>{v ? 'Ring' : 'Chain'}</Badge> },
]

export default function Lab() {
  const [searchParams] = useSearchParams()
  const [smiles, setSmiles] = useState(searchParams.get('smiles') || PRESET_MOLECULES[0].smiles)
  const [data, setData] = useState(null)
  const [loading, setLoading] = useState(false)
  const [errorInfo, setErrorInfo] = useState(null)
  const [viewMode, setViewMode] = useState('depict')
  const [chemMode, setChemMode] = useState('written')
  const [copiedMol, setCopiedMol] = useState(false)
  const [tab, setTab] = useState('atoms')

  const [showCompare, setShowCompare] = useState(false)
  const [smilesB, setSmilesB] = useState(COMPARE_PRESETS[0].smiles)
  const [tanimotoData, setTanimotoData] = useState(null)
  const [compareError, setCompareError] = useState('')
  const [comparing, setComparing] = useState(false)

  const parseReqId = useRef(0)
  const compareReqId = useRef(0)
  const parseHandle = useRef(null)
  const compareHandle = useRef(null)
  const typingTimer = useRef(null)
  const [parseStartedAt, setParseStartedAt] = useState(null)

  const runAnalysis = async (target) => {
    const reqId = ++parseReqId.current
    if (!target.trim()) {
      setErrorInfo(null)
      setLoading(false)
      return
    }
    setLoading(true)
    // one evaluation at a time: a new one cancels the previous, on the server too
    parseHandle.current?.cancel()
    const handle = newRequestHandle()
    parseHandle.current = handle
    setParseStartedAt(Date.now())
    try {
      const res = await api.analyzeSmiles(target, handle)
      if (reqId !== parseReqId.current) return
      setErrorInfo(null)
      setData(res)
      if (showCompare && smilesB.trim()) {
        runComparison(target, smilesB)
      }
    } catch (err) {
      if (reqId !== parseReqId.current || err.cancelled) return
      // Lean's own verdict is a 400 with a constructor; anything else (5xx, a
      // worker that died or timed out, no network) is not about the SMILES.
      const isParseError = err.status === 400 && err.details?.constructor !== undefined
      setErrorInfo(
        isParseError
          ? err.details
          : {
              error: err.message || 'No answer from the Lean server',
              constructor: 'ServiceError',
              isServiceError: true,
              explanation:
                'This is not a verdict on the SMILES: the request to the Lean server failed or timed out. Try again in a moment; if it keeps happening, the Lean worker on the server is down.',
              logs: [`POST /api/parse "${target}" --> ${err.message || 'no response'}`],
            }
      )
    } finally {
      if (reqId === parseReqId.current) {
        setLoading(false)
        parseHandle.current = null
      }
    }
  }

  const runComparison = async (a, b) => {
    const reqId = ++compareReqId.current
    if (!a?.trim() || !b?.trim()) {
      setCompareError('')
      setComparing(false)
      return
    }
    setCompareError('')
    setComparing(true)
    compareHandle.current?.cancel()
    const handle = newRequestHandle()
    compareHandle.current = handle
    try {
      const res = await api.compareTanimoto(a, b, handle)
      if (reqId !== compareReqId.current) return
      setTanimotoData(res)
    } catch (err) {
      if (reqId !== compareReqId.current || err.cancelled) return
      setCompareError(err.details?.error || err.message || 'Comparison failed')
    } finally {
      if (reqId === compareReqId.current) {
        setComparing(false)
      }
    }
  }

  useEffect(() => {
    runAnalysis(smiles)
  }, [])

  // Typing waits 250 ms for the next keystroke; a preset evaluates at once.
  const handleSmilesChange = (val, immediate = false) => {
    setSmiles(val)
    clearTimeout(typingTimer.current)
    if (immediate) runAnalysis(val)
    else typingTimer.current = setTimeout(() => runAnalysis(val), 250)
  }

  const cancelAnalysis = () => {
    clearTimeout(typingTimer.current)
    parseReqId.current += 1
    parseHandle.current?.cancel()
    parseHandle.current = null
    setLoading(false)
  }

  const handleSmilesBChange = (val) => {
    setSmilesB(val)
    runComparison(smiles, val)
  }

  const isSanitized = chemMode === 'sanitized' && Boolean(data?.aromatized?.ok)
  const mol = isSanitized ? { ...data, ...data.aromatized } : data

  const handleCopyMolBlock = () => {
    if (!mol?.molBlock) return
    navigator.clipboard.writeText(mol.molBlock)
    setCopiedMol(true)
    setTimeout(() => setCopiedMol(false), 1500)
  }

  const handleDownloadMolBlock = () => {
    if (!mol?.molBlock) return
    const blob = new Blob([mol.molBlock], { type: 'chemical/x-mdl-molfile' })
    const url = URL.createObjectURL(blob)
    const a = document.createElement('a')
    a.href = url
    a.download = `${(mol.canonicalSmiles || 'molecule').replace(/[^a-zA-Z0-9_-]/g, '_')}.mol`
    a.click()
    URL.revokeObjectURL(url)
  }

  const sharedSet = new Set(tanimotoData?.sharedBits || [])
  const activeLogs = errorInfo ? errorInfo.logs || [] : data?.logs || []
  const combinedLogs = [...activeLogs, ...(tanimotoData?.logs || [])]
  const diagnostics = buildDiagnostics(data, errorInfo)
  // The evaluation trace and the checks: first on the page when there is an
  // error to explain, last otherwise, so the drawing comes before the logs.
  const logPanel = (
    <LogConsole
      logs={combinedLogs}
      feedback={errorInfo ? errorInfo.leanFeedback : data?.leanFeedback}
      diagnostics={diagnostics}
      loading={loading}
    />
  )

  return (
    <div className="space-y-6">
      <SectionHeader
        title="SMILES Interpreter"
        description="Type any SMILES to evaluate canonical LeanSMILES, toggle between As-Written (M) and Sanitized (M.aromatize), inspect 2D depictions or V2000 Mol blocks, and compare Morgan fingerprints."
        right={
          loading && (
            <BusyBar
              label="Evaluating in Lean 4"
              startedAt={parseStartedAt}
              expectedMs={250 + 8 * smiles.length}
              onCancel={cancelAnalysis}
            />
          )
        }
      />

      <Card>
        <div className="relative flex items-center">
          <input
            value={smiles}
            onChange={(e) => handleSmilesChange(e.target.value)}
            placeholder="Write a SMILES string (e.g. Cn1cnc2c1c(=O)n(C)c(=O)n2C)..."
            className="w-full bg-slate-900/2 border border-slate-200/80 px-3.5 py-2.5 pr-10 rounded-xl font-mono text-xs text-slate-800 focus:outline-none focus:border-slate-400"
          />
          {loading && (
            <span className="absolute right-3.5 w-3.5 h-3.5 rounded-full border-2 border-slate-300 border-t-teal-600 animate-spin" />
          )}
        </div>

        <div className="flex flex-wrap gap-1.5 mt-3">
          {PRESET_MOLECULES.map((p) => (
            <button
              key={p.name}
              type="button"
              disabled={loading}
              onClick={() => handleSmilesChange(p.smiles, true)}
              className={`px-2.5 py-1 rounded-lg text-xs transition cursor-pointer disabled:opacity-40 disabled:cursor-not-allowed ${
                smiles === p.smiles
                  ? 'bg-slate-900 text-white font-medium'
                  : 'text-slate-500 hover:bg-slate-100 hover:text-slate-800'
              }`}
            >
              {p.name}
            </button>
          ))}
        </div>
      </Card>

      {errorInfo && logPanel}

      {mol && (
        <div className={`space-y-6 transition-opacity duration-150 ${loading || errorInfo ? 'opacity-50' : 'opacity-100'}`}>
          <div className="grid md:grid-cols-2 gap-6">
            <Card
              title={
                viewMode === 'depict'
                  ? '2D Molecule (LeanSMILES.Depict)'
                  : viewMode === 'graph'
                  ? 'SimpleGraph (Fin n)'
                  : 'MDL Mol Block (V2000)'
              }
              subtitle={`${mol.n} atoms · ${mol.numBonds} bonds · ${mol.totalHydrogens} hydrogens`}
              action={
                <div className="flex gap-1">
                  <Button
                    variant={viewMode === 'depict' ? 'primary' : 'secondary'}
                    onClick={() => setViewMode('depict')}
                    className="!px-2.5 !py-1"
                  >
                    Molecule
                  </Button>
                  <Button
                    variant={viewMode === 'graph' ? 'primary' : 'secondary'}
                    onClick={() => setViewMode('graph')}
                    className="!px-2.5 !py-1"
                  >
                    Graph (Fin n)
                  </Button>
                  <Button
                    variant={viewMode === 'molblock' ? 'primary' : 'secondary'}
                    onClick={() => setViewMode('molblock')}
                    className="!px-2.5 !py-1"
                  >
                    .mol
                  </Button>
                </div>
              }
            >
              {viewMode === 'molblock' ? (
                <div className="relative">
                  <div className="absolute top-2.5 right-2.5 flex gap-1">
                    <Button
                      variant="secondary"
                      onClick={handleCopyMolBlock}
                      className="!px-2 !py-1 inline-flex items-center gap-1"
                    >
                      {copiedMol ? <Check size={12} /> : <Copy size={12} />}
                      {copiedMol ? 'Copied' : 'Copy'}
                    </Button>
                    <Button
                      variant="secondary"
                      onClick={handleDownloadMolBlock}
                      className="!px-2 !py-1 inline-flex items-center gap-1"
                    >
                      <Download size={12} /> .mol
                    </Button>
                  </div>
                  <pre className="w-full h-60 overflow-auto rounded-xl bg-slate-900/2 border border-slate-200/60 p-3 text-[11px] font-mono text-slate-700 leading-snug">
                    {mol.molBlock}
                  </pre>
                </div>
              ) : (
                <MoleculeGraph
                  mode={viewMode}
                  svg={mol.svg}
                  atoms={mol.atoms}
                  bonds={mol.bonds}
                  coordinates={mol.coordinates}
                />
              )}
            </Card>

            <Card
              title="Canonical LeanSMILES"
              subtitle="Color refinement + exhaustive tie-breaking (Mol.canonicalSmiles)"
              action={
                data.aromatized?.ok && (
                  <div className="flex gap-1">
                    <Button
                      variant={!isSanitized ? 'primary' : 'secondary'}
                      onClick={() => setChemMode('written')}
                      className="!px-2.5 !py-1"
                    >
                      As-Written
                    </Button>
                    <Button
                      variant={isSanitized ? 'primary' : 'secondary'}
                      onClick={() => setChemMode('sanitized')}
                      className="!px-2.5 !py-1"
                    >
                      Sanitized
                    </Button>
                  </div>
                )
              }
            >
              <div className="space-y-3">
                <div onClick={() => setChemMode('written')} className="cursor-pointer">
                  <p className="text-[11px] text-slate-400 mb-1">As-Written Canonical SMILES</p>
                  <div
                    className={`p-3 rounded-xl bg-slate-900/2 border font-mono text-xs break-all transition ${
                      !isSanitized
                        ? 'border-teal-500/50 text-teal-700 font-medium'
                        : 'border-slate-200/70 text-slate-600'
                    }`}
                  >
                    {data.canonicalSmiles}
                  </div>
                </div>

                {data.aromatized?.ok && (
                  <div onClick={() => setChemMode('sanitized')} className="cursor-pointer">
                    <p className="text-[11px] text-slate-400 mb-1">
                      RDKit cleanUp + Hückel 4n+2 Sanitized (Mol.aromatize)
                    </p>
                    <div
                      className={`p-3 rounded-xl bg-slate-900/2 border font-mono text-xs break-all transition ${
                        isSanitized
                          ? 'border-teal-500/50 text-teal-700 font-medium'
                          : 'border-slate-200/70 text-slate-600'
                      }`}
                    >
                      {data.aromatized.canonicalSmiles}
                    </div>
                  </div>
                )}

                <div className="pt-1">
                  <p className="text-[11px] text-slate-400 mb-1.5">Tokens ({mol.tokens.length})</p>
                  <div className="flex flex-wrap gap-1 max-h-24 overflow-y-auto">
                    {mol.tokens.map((t, i) => (
                      <span
                        key={i}
                        className="px-2 py-0.5 rounded bg-slate-100/80 text-slate-600 font-mono text-[11px]"
                      >
                        {t.show}
                      </span>
                    ))}
                  </div>
                </div>
              </div>
            </Card>
          </div>

          <Card
            title="Morgan Fingerprint (Radius 2, 2048 Bits) & Tanimoto"
            subtitle={`${mol.morganBits.length} active bits set · Proved order-invariant (Molecule.morganBits_relabel)`}
            action={
              !showCompare ? (
                <Button
                  variant="secondary"
                  onClick={() => {
                    setShowCompare(true)
                    runComparison(smiles, smilesB)
                  }}
                  className="inline-flex items-center gap-1"
                >
                  <Plus size={13} /> Compare SMILES (Tanimoto)
                </Button>
              ) : (
                <Button
                  variant="secondary"
                  onClick={() => {
                    setShowCompare(false)
                    setTanimotoData(null)
                    setCompareError('')
                  }}
                  className="inline-flex items-center gap-1"
                >
                  <X size={13} /> Close Comparison
                </Button>
              )
            }
          >
            <div className="flex flex-wrap gap-1.5">
              {mol.morganBits.map((bit) => (
                <Badge key={bit} active={showCompare && sharedSet.has(bit)}>
                  {bit}
                </Badge>
              ))}
            </div>

            {showCompare && (
              <div className="mt-5 pt-5 border-t border-slate-200/60 space-y-4">
                <div className="relative flex items-center">
                  <input
                    value={smilesB}
                    onChange={(e) => handleSmilesBChange(e.target.value)}
                    placeholder="Second SMILES for Tanimoto comparison..."
                    className="w-full bg-slate-900/2 border border-slate-200/80 px-3.5 py-2.5 pr-10 rounded-xl font-mono text-xs text-slate-800 focus:outline-none focus:border-slate-400"
                  />
                  {comparing && (
                    <span className="absolute right-3.5 w-3.5 h-3.5 rounded-full border-2 border-slate-300 border-t-teal-600 animate-spin" />
                  )}
                </div>

                <div className="flex flex-wrap items-center gap-1.5">
                  <span className="text-[11px] text-slate-400 mr-1">Compare with:</span>
                  {COMPARE_PRESETS.map((p) => (
                    <button
                      key={p.label}
                      type="button"
                      disabled={comparing}
                      onClick={() => handleSmilesBChange(p.smiles)}
                      className={`px-2.5 py-1 rounded-lg text-xs transition cursor-pointer disabled:opacity-40 disabled:cursor-not-allowed ${
                        smilesB === p.smiles
                          ? 'bg-slate-900 text-white font-medium'
                          : 'text-slate-500 hover:bg-slate-100 hover:text-slate-800'
                      }`}
                    >
                      {p.label}
                    </button>
                  ))}
                </div>

                {compareError && (
                  <p className="text-xs text-rose-600 font-mono">{compareError}</p>
                )}

                {tanimotoData && (
                  <div className={`grid sm:grid-cols-2 gap-4 pt-1 transition-opacity duration-150 ${comparing ? 'opacity-60' : 'opacity-100'}`}>
                    <div className="p-4 rounded-xl bg-slate-900/2 border border-slate-200/70">
                      <p className="text-xs text-slate-400">Exact Tanimoto Similarity (over ℚ)</p>
                      <div className="flex items-baseline gap-3 mt-1">
                        <span className="text-2xl font-semibold font-mono text-slate-900">
                          {(tanimotoData.tanimoto * 100).toFixed(1)}%
                        </span>
                        <span className="text-xs font-mono text-teal-700">
                          {tanimotoData.rational} ({tanimotoData.intersection} shared / {tanimotoData.union} union bits)
                        </span>
                      </div>
                      <p className="text-[11px] text-slate-400 mt-1.5 font-mono truncate">
                        Canonical B: {tanimotoData.molB.canonicalSmiles}
                      </p>
                    </div>

                    <div className="p-4 rounded-xl bg-slate-900/2 border border-slate-200/70">
                      <p className="text-xs text-slate-400 mb-2">
                        Molecule B Morgan Bits ({tanimotoData.molB.morganBits.length})
                      </p>
                      <div className="flex flex-wrap gap-1.5 max-h-28 overflow-y-auto">
                        {tanimotoData.molB.morganBits.map((bit) => (
                          <Badge key={bit} active={sharedSet.has(bit)}>
                            {bit}
                          </Badge>
                        ))}
                      </div>
                    </div>
                  </div>
                )}
              </div>
            )}
          </Card>

          <Card
            title={tab === 'atoms' ? `Atoms (Fin ${mol.n})` : 'BondMatrix n (over ℚ)'}
            action={
              <div className="flex gap-1">
                <Button variant={tab === 'atoms' ? 'primary' : 'secondary'} onClick={() => setTab('atoms')}>
                  Atoms
                </Button>
                <Button variant={tab === 'matrix' ? 'primary' : 'secondary'} onClick={() => setTab('matrix')}>
                  Matrix ℚ
                </Button>
              </div>
            }
          >
            {tab === 'atoms' ? (
              <DataTable maxHeight="max-h-72" columns={ATOM_COLUMNS} rows={mol.atoms} />
            ) : (
              <div className="overflow-auto max-h-72 rounded-xl border border-slate-200/60 bg-white/50 p-2">
                <table className="w-full text-center font-mono text-xs">
                  <thead>
                    <tr className="text-slate-400">
                      <th className="p-1.5">#</th>
                      {mol.atoms.map((a) => (
                        <th key={a.idx} className="p-1.5 font-normal">{a.idx}</th>
                      ))}
                    </tr>
                  </thead>
                  <tbody>
                    {mol.adjMatrix.map((row, rIdx) => (
                      <tr key={rIdx}>
                        <td className="p-1.5 text-slate-400">{rIdx}</td>
                        {row.map((val, cIdx) => (
                          <td
                            key={cIdx}
                            className={`p-1.5 rounded ${
                              val !== '0' ? 'bg-teal-50 text-teal-700 font-semibold' : 'text-slate-300'
                            }`}
                          >
                            {val}
                          </td>
                        ))}
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            )}
          </Card>
        </div>
      )}

      {!errorInfo && logPanel}
    </div>
  )
}
