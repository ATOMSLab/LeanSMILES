import express from 'express'
import cors from 'cors'
import leanRoutes from './routes/leanRoutes.js'

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

app.get('/health', (_req, res) => {
  res.json({ status: 'ok' })
})

app.get('/api/health', (_req, res) => {
  res.json({ status: 'ok' })
})

app.use('/api', leanRoutes)

app.listen(PORT, '0.0.0.0', () => {
  console.log(`LeanSMILES API server running on http://0.0.0.0:${PORT}`)
})
