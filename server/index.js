import express from 'express'
import cors from 'cors'
import leanRoutes, { prewarmBuiltinDatasets } from './routes/leanRoutes.js'
import { leanWorkerStatus } from './workers/leanWorker.js'

const app = express()
const PORT = process.env.PORT || 8000

const corsOptions = {
  origin: true,
  methods: ['GET', 'POST', 'PUT', 'PATCH', 'DELETE', 'OPTIONS'],
  allowedHeaders: ['Content-Type', 'Authorization', 'Accept', 'Origin', 'X-Requested-With'],
  credentials: true,
  optionsSuccessStatus: 200,
}

app.use(cors(corsOptions))
app.options('*', cors(corsOptions))
app.use(express.json({ limit: '10mb' }))

app.get('/', (_req, res) => {
  res.json({ status: 'ok', service: 'LeanSMILES API' })
})

// `worker` says whether the Lean evaluator is up: the service answers cached
// requests from disk even when it is not, so `status` alone can mislead.
app.get('/health', (_req, res) => {
  res.json({ status: 'ok', worker: leanWorkerStatus() })
})

app.get('/api/health', (_req, res) => {
  res.json({ status: 'ok', worker: leanWorkerStatus() })
})

app.use('/api', leanRoutes)

app.listen(PORT, '0.0.0.0', () => {
  console.log(`LeanSMILES API server running on http://0.0.0.0:${PORT}`)
  if (process.env.LEAN_PREWARM !== '0') prewarmBuiltinDatasets()
})
