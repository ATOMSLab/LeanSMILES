import express from 'express'
import cors from 'cors'
import leanRoutes from './routes/leanRoutes.js'

const app = express()
const PORT = process.env.PORT || 8000

app.use(cors())
app.use(express.json())

app.use('/api', leanRoutes)

app.listen(PORT, () => {
  console.log(`leanSmiles API server running on http://localhost:${PORT}`)
})
