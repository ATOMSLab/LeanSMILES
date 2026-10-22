import React from 'react'
import Navbar from './components/Navbar'
import AppRoutes from './routes/AppRoutes'
import api from './middleware/api'

export default function App() {
  return (
    <div className="min-h-screen flex flex-col" data-api-ready={Boolean(api)}>
      <Navbar />
      <main className="flex-1 max-w-5xl w-full mx-auto px-6 py-10">
        <AppRoutes />
      </main>
      <footer className="py-6 text-center text-xs text-slate-400">
        leanSmiles · ATOMS Lab
      </footer>
    </div>
  )
}
