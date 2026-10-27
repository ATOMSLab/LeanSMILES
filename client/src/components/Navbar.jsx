import React from 'react'
import { NavLink } from 'react-router-dom'
import { Atom } from 'lucide-react'

const LINKS = [
  { to: '/', label: 'Overview' },
  { to: '/lab', label: 'SMILES Interpreter' },
  { to: '/datasets', label: 'Regression' },
]

export default function Navbar() {
  return (
    <header className="sticky top-0 z-30 glass border-x-0 border-t-0">
      <div className="max-w-5xl mx-auto px-4 sm:px-6 h-14 flex items-center justify-between gap-2">
        <NavLink to="/" className="flex items-center gap-1.5 sm:gap-2 font-semibold text-sm sm:text-base tracking-tight text-slate-900 shrink-0">
          <Atom size={18} className="text-teal-600 shrink-0" />
          <span>LeanSMILES</span>
        </NavLink>

        <nav className="flex items-center gap-0.5 sm:gap-1 overflow-x-auto">
          {LINKS.map((l) => (
            <NavLink
              key={l.to}
              to={l.to}
              end={l.to === '/'}
              className={({ isActive }) =>
                `px-2.5 sm:px-3 py-1.5 rounded-lg text-xs font-medium whitespace-nowrap transition ${
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
