import React from 'react'
import Navbar from './components/Navbar'
import AppRoutes from './routes/AppRoutes'
import api from './middleware/api'

export default function App() {
  return (
    <div className="min-h-screen flex flex-col overflow-x-hidden" data-api-ready={Boolean(api)}>
      <Navbar />
      <main className="flex-1 max-w-5xl w-full mx-auto px-4 sm:px-6 py-6 sm:py-10 min-w-0">
        <AppRoutes />
      </main>
      <footer className="py-6 text-center text-xs text-slate-400">
        LeanSMILES · ATOMS Lab
      </footer>
    </div>
  )
}
