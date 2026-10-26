import { Router } from 'express'
import fs from 'fs'
import path from 'path'
import crypto from 'crypto'
import { fileURLToPath } from 'url'
import { leanTemplates, explainParseError } from '../templates/leanTemplates.js'
import { runLean } from '../workers/leanWorker.js'

const __dirname = path.dirname(fileURLToPath(import.meta.url))
const REPO_ROOT = path.resolve(__dirname, '../..')
const CACHE_DIR = path.resolve(__dirname, '../.cache')

const router = Router()

function splitCsvLine(line) {
  const out = []
  let cur = ''
  let inQuotes = false
  for (let i = 0; i < line.length; i++) {
    const ch = line[i]
    if (ch === '"') {
      inQuotes = !inQuotes
    } else if (ch === ',' && !inQuotes) {
      out.push(cur.trim())
      cur = ''
    } else {
      cur += ch
    }
  }
  out.push(cur.trim())
  return out
}

function buildDatasetTsv(datasetId, customRows) {
  fs.mkdirSync(CACHE_DIR, { recursive: true })
  const maxRows = 205

  if (Array.isArray(customRows) && customRows.length > 0) {
    const sliced = customRows.slice(0, maxRows)
    const tsvContent = sliced
      .map((r, idx) => {
        const name = String(r.name || `Mol_${idx + 1}`).replace(/[\t\r\n]/g, ' ')
        const smiles = String(r.smiles || '').replace(/[\t\r\n]/g, '').trim()
        const target = String(r.target ?? '').replace(/[\t\r\n]/g, '').trim()
        const split = r.split || (idx % 5 === 0 ? 'test' : 'train')
        return `${name}\t${smiles}\t${target}\t${split}`
      })
      .filter((line) => {
        const parts = line.split('\t')
        return parts[1] && parts[2] && !Number.isNaN(Number(parts[2]))
      })
      .join('\n')

    const hash = crypto.createHash('md5').update(tsvContent).digest('hex').slice(0, 10)
    const relPath = `server/.cache/fit-custom-${hash}.tsv`
    fs.writeFileSync(path.join(REPO_ROOT, relPath), tsvContent, 'utf8')
    return relPath
  }

  if (datasetId === 'egfr' || datasetId === 'egfr-actives' || datasetId === 'egfr-fda') {
    const raw = fs.readFileSync(path.join(REPO_ROOT, 'datasets/egfr-classification.csv'), 'utf8')
    const lines = raw.split(/\r?\n/).slice(1).filter((l) => l.trim())
    const rows = []
    for (const line of lines) {
      const [name, smiles, active, split] = line.split(',')
      if ((split === 'train' || split === 'test') && (active === '0' || active === '1')) {
        rows.push(`${name}\t${smiles}\t${active}\t${split}`)
      }
    }
    const relPath = `server/.cache/fit-egfr-${maxRows}.tsv`
    fs.writeFileSync(path.join(REPO_ROOT, relPath), rows.slice(0, maxRows).join('\n'), 'utf8')
    return relPath
  }

  if (datasetId === 'thermo') {
    const raw = fs.readFileSync(path.join(REPO_ROOT, 'datasets/ThermoPropertiesSMILES.csv'), 'utf8')
    const lines = raw.split(/\r?\n/).slice(1).filter((l) => l.trim())
    const rows = []
    for (let i = 0; i < lines.length && rows.length < maxRows; i++) {
      const cells = splitCsvLine(lines[i])
      const name = cells[0] || `Compound_${i + 1}`
      const bp = cells[4]
      const smiles = cells[6]
      if (smiles && bp && !Number.isNaN(Number(bp))) {
        const split = rows.length % 5 === 0 ? 'test' : 'train'
        rows.push(`${name}\t${smiles}\t${bp}\t${split}`)
      }
    }
    const relPath = `server/.cache/fit-thermo-${maxRows}.tsv`
    fs.writeFileSync(path.join(REPO_ROOT, relPath), rows.join('\n'), 'utf8')
    return relPath
  }

  const raw = fs.readFileSync(path.join(REPO_ROOT, 'datasets/delaney-ridge.csv'), 'utf8')
  const lines = raw.split(/\r?\n/).slice(1).filter((l) => l.trim())
  const rows = []
  for (let i = 0; i < lines.length && rows.length < maxRows; i++) {
    const [name, smiles, logS, split] = lines[i].split(',')
    if (smiles && logS && (split === 'train' || split === 'test')) {
      rows.push(`${name}\t${smiles}\t${logS}\t${split}`)
    }
  }
  const relPath = `server/.cache/fit-delaney-${maxRows}.tsv`
  fs.writeFileSync(path.join(REPO_ROOT, relPath), rows.join('\n'), 'utf8')
  return relPath
}

router.post('/parse', async (req, res) => {
  const { smiles } = req.body || {}
  if (!smiles || !smiles.trim()) {
    return res.status(400).json({ error: 'SMILES string is required' })
  }

  try {
    const code = leanTemplates.parseMolecule(smiles.trim())
    const result = await runLean(code)
    if (!result.ok) {
      return res.status(400).json({
        ok: false,
        smiles: smiles.trim(),
        error: result.error || 'Parse error',
        constructor: result.constructor || '',
        isGrammarDeviation: Boolean(result.isGrammarDeviation),
        explanation: explainParseError(result.constructor, result.error),
        logs: result.logs || [],
        leanFeedback: result.leanFeedback,
      })
    }
    res.json(result)
  } catch (err) {
    res.status(500).json({ error: err.message })
  }
})

router.post('/tanimoto', async (req, res) => {
  const { smilesA, smilesB } = req.body || {}
  if (!smilesA || !smilesB) {
    return res.status(400).json({ error: 'Both smilesA and smilesB are required' })
  }

  try {
    const code = leanTemplates.compareTanimoto(smilesA.trim(), smilesB.trim())
    const result = await runLean(code)
    if (!result.ok) {
      return res.status(400).json({
        ok: false,
        error: result.error || 'Comparison failed',
        constructor: result.constructor || '',
        explanation: explainParseError(result.constructor, result.error),
        logs: result.logs || [],
        leanFeedback: result.leanFeedback,
      })
    }
    res.json(result)
  } catch (err) {
    res.status(500).json({ error: err.message })
  }
})

router.get('/datasets', async (req, res) => {
  const datasetId = req.query.id || 'delaney'
  try {
    const code = leanTemplates.loadDataset(datasetId)
    const result = await runLean(code)
    res.json(result)
  } catch (err) {
    res.status(500).json({ error: err.message })
  }
})

router.post('/pipeline/fit', async (req, res) => {
  const {
    datasetId = 'delaney',
    customRows = null,
    modelType = 'sparse-ridge',
    alpha = '1.0',
    targetLabel = 'log solubility (log mol/L)',
  } = req.body || {}

  try {
    const tsvPath = buildDatasetTsv(datasetId, customRows, modelType)
    const code = leanTemplates.fitPipeline(tsvPath, modelType, String(alpha), targetLabel)
    const result = await runLean(code)
    if (!result.ok) {
      return res.status(400).json(result)
    }
    res.json(result)
  } catch (err) {
    res.status(500).json({ ok: false, error: err.message })
  }
})

export default router
