import React, { useState, useEffect, useRef } from 'react'
import { useSearchParams } from 'react-router-dom'
import { Plus, X } from 'lucide-react'
import api, { PRESET_MOLECULES } from '../middleware/api'
import {
  Card,
  Badge,
  Button,
  SectionHeader,
  DataTable,
  SpinnerPill,
  LogConsole,
} from '../components/UI'
import MoleculeGraph from '../components/MoleculeGraph'

const COMPARE_PRESETS = [
  { label: 'Theobromine', smiles: 'Cn1cnc2c1c(=O)[nH]c(=O)n2C' },
  { label: 'Propanol', smiles: 'CCCO' },
  { label: 'Ethanol (OCC)', smiles: 'OCC' },
]

export default function Lab() {
  const [searchParams] = useSearchParams()
  const [smiles, setSmiles] = useState(searchParams.get('smiles') || PRESET_MOLECULES[0].smiles)
  const [data, setData] = useState(null)
  const [loading, setLoading] = useState(false)
  const [errorInfo, setErrorInfo] = useState(null)
  const [viewMode, setViewMode] = useState('depict')
  const [tab, setTab] = useState('atoms')

  const [showCompare, setShowCompare] = useState(false)
  const [smilesB, setSmilesB] = useState(COMPARE_PRESETS[0].smiles)
  const [tanimotoData, setTanimotoData] = useState(null)
  const [compareError, setCompareError] = useState('')
  const [comparing, setComparing] = useState(false)

  const parseReqId = useRef(0)
  const compareReqId = useRef(0)

  const runAnalysis = async (target) => {
    const reqId = ++parseReqId.current
    if (!target.trim()) {
      setErrorInfo(null)
      setLoading(false)
      return
    }
    setLoading(true)
    try {
      const res = await api.analyzeSmiles(target)
      if (reqId !== parseReqId.current) return
      setErrorInfo(null)
      setData(res)
      if (showCompare && smilesB.trim()) {
        runComparison(target, smilesB)
      }
    } catch (err) {
      if (reqId !== parseReqId.current) return
      setErrorInfo(
        err.details || {
          error: err.message || 'Invalid SMILES syntax',
          constructor: 'ParseError',
          explanation: 'Check parentheses, ring closures, and atom symbols.',
          logs: [`parse "${target}" --> Except.error`],
        }
      )
    } finally {
      if (reqId === parseReqId.current) {
        setLoading(false)
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
    try {
      const res = await api.compareTanimoto(a, b)
      if (reqId !== compareReqId.current) return
      setTanimotoData(res)
    } catch (err) {
      if (reqId !== compareReqId.current) return
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

  const handleSmilesChange = (val) => {
    setSmiles(val)
    runAnalysis(val)
  }

  const handleSmilesBChange = (val) => {
    setSmilesB(val)
    runComparison(smiles, val)
  }

  const sharedSet = new Set(tanimotoData?.sharedBits || [])
  const activeLogs = errorInfo ? errorInfo.logs || [] : data?.logs || []
  const combinedLogs = [...activeLogs, ...(tanimotoData?.logs || [])]

  let diagnostics = null
  if (errorInfo) {
    diagnostics = {
      status: 'error',
      items: [
        {
          type: 'error',
          label: errorInfo.isGrammarDeviation ? 'OpenSMILES §2.2 Rule' : 'SMILES Syntax Error',
          tag: errorInfo.constructor || 'ParseError',
          detail: errorInfo.error,
        },
        ...(errorInfo.explanation
          ? [
              {
                type: 'warn',
                label: 'How to Fix',
                tag: 'LeanSMILES.SMILES.Parse',
                detail: errorInfo.explanation,
              },
            ]
          : []),
      ],
    }
  } else if (data) {
    const chargeOk = data.chargeCheck?.ok !== false
    const aromOk = data.aromatized?.ok !== false
    diagnostics = {
      status: !chargeOk || !aromOk ? 'warn' : 'ok',
      items: [
        {
          type: 'ok',
          label: 'OpenSMILES Syntax',
          tag: `Molecule ${data.n}`,
          detail: `Parsed ${data.tokens.length} tokens into ${data.n} atoms and ${data.numBonds} bonds.`,
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
          label: 'Hückel 4n+2 Aromaticity',
          tag: 'Mol.aromatize',
          detail: aromOk
            ? `Canonical aromatized: ${data.aromatized?.canonicalSmiles}`
            : data.aromatized?.message,
        },
      ],
    }
  }

  return (
    <div className="space-y-6">
      <SectionHeader
        title="SMILES Interpreter"
        description="Type any SMILES to immediately evaluate canonical LeanSMILES, toggle between Lean's 2D chemical depiction and SimpleGraph (Fin n), inspect Morgan fingerprints, and compare Tanimoto similarity."
        right={loading && <SpinnerPill label="Evaluating in Lean 4..." />}
      />

      <Card>
        <div className="relative flex items-center">
          <input
            value={smiles}
            onChange={(e) => handleSmilesChange(e.target.value)}
            placeholder="Write a SMILES string (e.g. Cn1cnc2c1c(=O)n(C)c(=O)n2C)..."
            className="w-full bg-slate-900/[0.02] border border-slate-200/80 px-3.5 py-2.5 pr-10 rounded-xl font-mono text-xs text-slate-800 focus:outline-none focus:border-slate-400"
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
              onClick={() => handleSmilesChange(p.smiles)}
              className={`px-2.5 py-1 rounded-lg text-xs transition cursor-pointer ${
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

      <LogConsole
        logs={combinedLogs}
        feedback={errorInfo ? errorInfo.leanFeedback : data?.leanFeedback}
        diagnostics={diagnostics}
        loading={loading}
      />

      {data && (
        <div className={`space-y-6 transition-opacity duration-150 ${loading || errorInfo ? 'opacity-50' : 'opacity-100'}`}>
          <div className="grid md:grid-cols-2 gap-6">
            <Card
              title="Canonical LeanSMILES"
              subtitle="Color refinement + exhaustive tie-breaking (Mol.canonicalSmiles)"
            >
              <div className="space-y-3">
                <div>
                  <p className="text-[11px] text-slate-400 mb-1">As-Written Canonical SMILES</p>
                  <div className="p-3 rounded-xl bg-slate-900/[0.02] border border-slate-200/70 font-mono text-xs text-teal-700 font-medium break-all">
                    {data.canonicalSmiles}
                  </div>
                </div>

                {data.aromatized?.ok && (
                  <div>
                    <p className="text-[11px] text-slate-400 mb-1">
                      RDKit Hückel 4n+2 Aromatized (Mol.aromatize)
                    </p>
                    <div className="p-3 rounded-xl bg-slate-900/[0.02] border border-slate-200/70 font-mono text-xs text-slate-700 break-all">
                      {data.aromatized.canonicalSmiles}
                    </div>
                  </div>
                )}

                <div className="pt-1">
                  <p className="text-[11px] text-slate-400 mb-1.5">Tokens ({data.tokens.length})</p>
                  <div className="flex flex-wrap gap-1 max-h-24 overflow-y-auto">
                    {data.tokens.map((t, i) => (
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

            <Card
              title={viewMode === 'depict' ? '2D Molecule (LeanSMILES.Depict)' : 'SimpleGraph (Fin n)'}
              subtitle={`${data.n} atoms · ${data.numBonds} bonds · ${data.totalHydrogens} hydrogens`}
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
                </div>
              }
            >
              <MoleculeGraph
                mode={viewMode}
                svg={data.svg}
                atoms={data.atoms}
                bonds={data.bonds}
                coordinates={data.coordinates}
              />
            </Card>
          </div>

          <Card
            title="Morgan Fingerprint (Radius 2, 2048 Bits) & Tanimoto"
            subtitle={`${data.morganBits.length} active bits set · Proved order-invariant (Molecule.morganBits_relabel)`}
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
              {data.morganBits.map((bit) => (
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
                    className="w-full bg-slate-900/[0.02] border border-slate-200/80 px-3.5 py-2.5 pr-10 rounded-xl font-mono text-xs text-slate-800 focus:outline-none focus:border-slate-400"
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
                      onClick={() => handleSmilesBChange(p.smiles)}
                      className={`px-2.5 py-1 rounded-lg text-xs transition cursor-pointer ${
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
                    <div className="p-4 rounded-xl bg-slate-900/[0.02] border border-slate-200/70">
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

                    <div className="p-4 rounded-xl bg-slate-900/[0.02] border border-slate-200/70">
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
            title={tab === 'atoms' ? `Atoms (Fin ${data.n})` : 'BondMatrix n (over ℚ)'}
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
              <DataTable
                maxHeight="max-h-72"
                columns={[
                  { key: 'idx', label: 'Fin n', render: (v) => <code className="text-slate-400">{v}</code> },
                  { key: 'raw', label: 'Token', render: (v) => <code className="font-mono text-slate-800">{v}</code> },
                  { key: 'symbol', label: 'Element' },
                  { key: 'degree', label: 'Degree' },
                  { key: 'totalH', label: 'Hydrogens' },
                  { key: 'charge', label: 'Charge', render: (v) => <code className="font-mono">{v > 0 ? `+${v}` : v}</code> },
                  { key: 'inRing', label: 'Topology', render: (v) => <Badge active={v}>{v ? 'Ring' : 'Chain'}</Badge> },
                ]}
                rows={data.atoms}
              />
            ) : (
              <div className="overflow-auto max-h-72 rounded-xl border border-slate-200/60 bg-white/50 p-2">
                <table className="w-full text-center font-mono text-xs">
                  <thead>
                    <tr className="text-slate-400">
                      <th className="p-1.5">#</th>
                      {data.atoms.map((a) => (
                        <th key={a.idx} className="p-1.5 font-normal">{a.idx}</th>
                      ))}
                    </tr>
                  </thead>
                  <tbody>
                    {data.adjMatrix.map((row, rIdx) => (
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
    </div>
  )
}
