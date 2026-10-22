import React, { useState, useEffect } from 'react'
import { useNavigate } from 'react-router-dom'
import api from '../middleware/api'
import { Card, Badge, Button, SectionHeader, DataTable, SpinnerPill, LogConsole } from '../components/UI'

const DATASET_TABS = [
  { id: 'delaney', label: 'Delaney ESOL (datasets/delaney-processed.csv)' },
  { id: 'egfr-fda', label: 'EGFR FDA Drugs (datasets/EGFR-FDA.csv)' },
  { id: 'egfr-actives', label: 'ChEMBL EGFR Actives' },
  { id: 'thermo', label: 'ThermoProperties SMILES' },
]

export default function Datasets() {
  const [datasetId, setDatasetId] = useState('delaney')
  const [query, setQuery] = useState('')
  const [loading, setLoading] = useState(false)
  const [state, setState] = useState({ rows: [], totalCount: 0, logs: [], leanFeedback: null })
  const navigate = useNavigate()

  const loadDataset = async (id) => {
    setDatasetId(id)
    setLoading(true)
    try {
      const res = await api.getDatasets(id)
      setState(res)
    } finally {
      setLoading(false)
    }
  }

  useEffect(() => {
    loadDataset('delaney')
  }, [])

  const rows = state.rows || []
  const filtered = rows.filter(
    (d) =>
      d.name?.toLowerCase().includes(query.toLowerCase()) ||
      d.smiles?.toLowerCase().includes(query.toLowerCase()) ||
      d.canonicalSmiles?.toLowerCase().includes(query.toLowerCase())
  )

  return (
    <div className="space-y-6">
      <SectionHeader
        title="Datasets"
        description="Real CSV datasets parsed directly by Lean's CSVparser and SMILES.parse into Molecule n and canonicalSmiles."
        right={loading && <SpinnerPill label="Parsing CSV in Lean 4..." />}
      />

      <Card
        title="Lean 4 CSV Datasets (CSVparser.lean)"
        subtitle={
          state.totalCount
            ? `${state.totalCount} total rows in CSV · Scrollable table of parsed Molecule n & canonicalSmiles`
            : 'Select a dataset to parse in Lean 4'
        }
        action={
          <div className="flex items-center gap-2">
            {loading && <SpinnerPill label="Loading..." />}
            <input
              value={query}
              onChange={(e) => setQuery(e.target.value)}
              placeholder="Filter rows..."
              className="px-3 py-1.5 rounded-xl bg-slate-900/[0.02] border border-slate-200/80 text-xs focus:outline-none"
            />
          </div>
        }
      >
        <div className="flex flex-wrap gap-1.5 mb-4">
          {DATASET_TABS.map((t) => (
            <button
              key={t.id}
              type="button"
              onClick={() => loadDataset(t.id)}
              className={`px-3 py-1.5 rounded-xl text-xs transition cursor-pointer ${
                datasetId === t.id
                  ? 'bg-slate-900 text-white font-medium'
                  : 'bg-slate-100/80 text-slate-600 hover:bg-slate-200/70'
              }`}
            >
              {t.label}
            </button>
          ))}
        </div>

        <div className={`transition-opacity duration-150 ${loading ? 'opacity-55' : 'opacity-100'}`}>
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
                label: rows[0]?.metricLabel || 'Feature',
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

      <LogConsole logs={state.logs} feedback={state.leanFeedback} loading={loading} />
    </div>
  )
}
