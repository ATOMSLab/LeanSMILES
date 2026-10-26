import express from 'express'
import cors from 'cors'
import leanRoutes from './routes/leanRoutes.js'

const app = express()
const PORT = process.env.PORT || 8000

app.use(cors())
app.use(express.json({ limit: '10mb' }))

app.get('/', (_req, res) => {
  res.json({ status: 'ok', service: 'LeanSMILES API' })
})

app.get('/health', (_req, res) => {
  res.json({ status: 'ok' })
})

app.get('/api/health', (_req, res) => {
  res.json({ status: 'ok' })
})

app.use('/api', leanRoutes)

app.listen(PORT, '0.0.0.0', () => {
  console.log(`leanSmiles API server running on http://0.0.0.0:${PORT}`)
})
