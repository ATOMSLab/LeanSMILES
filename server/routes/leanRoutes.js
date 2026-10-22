import { Router } from 'express'
import { leanTemplates, explainParseError } from '../templates/leanTemplates.js'
import { runLean } from '../workers/leanWorker.js'

const router = Router()

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

export default router
