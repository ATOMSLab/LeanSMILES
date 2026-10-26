import React from 'react'
import { NavLink } from 'react-router-dom'
import { Atom } from 'lucide-react'

const LINKS = [
  { to: '/', label: 'Overview' },
  { to: '/lab', label: 'SMILES Interpreter' },
  { to: '/datasets', label: 'Data Pipes' },
]

export default function Navbar() {
  return (
    <header className="sticky top-0 z-30 glass border-x-0 border-t-0">
      <div className="max-w-5xl mx-auto px-6 h-14 flex items-center justify-between">
        <NavLink to="/" className="flex items-center gap-2 font-semibold text-base tracking-tight text-slate-900">
          <Atom size={18} className="text-teal-600" />
          <span>leanSmiles</span>
        </NavLink>

        <nav className="flex items-center gap-1">
          {LINKS.map((l) => (
            <NavLink
              key={l.to}
              to={l.to}
              end={l.to === '/'}
              className={({ isActive }) =>
                `px-3 py-1.5 rounded-lg text-xs font-medium transition ${
                  isActive
                    ? 'bg-slate-900/5 text-slate-900'
                    : 'text-slate-500 hover:text-slate-900'
                }`
              }
            >
              {l.label}
            </NavLink>
          ))}
        </nav>
      </div>
    </header>
  )
}
