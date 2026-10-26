import React from 'react'

export default function MoleculeGraph({ mode = 'depict', svg = '', atoms = [], bonds = [], coordinates = [] }) {
  const n = atoms.length
  if (!n) return null

  if (mode === 'depict' && svg) {
    return (
      <div className="w-full h-60 rounded-xl bg-slate-900/1.5 border border-slate-200/60 flex items-center justify-center p-4 overflow-hidden">
        <div
          className="w-full h-full flex items-center justify-center [&>svg]:max-h-52 [&>svg]:max-w-full [&>svg]:w-auto [&>svg]:h-auto"
          dangerouslySetInnerHTML={{ __html: svg }}
        />
      </div>
    )
  }

  let coords = []
  if (coordinates && coordinates.length === n && n > 1) {
    const xs = coordinates.map((c) => c.x)
    const ys = coordinates.map((c) => c.y)
    const minX = Math.min(...xs)
    const maxX = Math.max(...xs)
    const minY = Math.min(...ys)
    const maxY = Math.max(...ys)
    const spanX = Math.max(maxX - minX, 1e-3)
    const spanY = Math.max(maxY - minY, 1e-3)
    const pad = 34 
    const availW = 360 - 2 * pad
    const availH = 240 - 2 * pad
    const scale = Math.min(availW / spanX, availH / spanY, 44)
    const w = spanX * scale
    const h = spanY * scale
    const offX = (360 - w) / 2
    const offY = (240 - h) / 2
    coords = coordinates.map((c) => ({
      x: offX + (c.x - minX) * scale,
      y: offY + (maxY - c.y) * scale,
    }))
  } else {
    const cx = 180
    const cy = 120
    const r = Math.min(84, Math.max(46, n * 6.5))
    coords = atoms.map((_, i) => {
      const angle = (2 * Math.PI * i) / n - Math.PI / 2
      return {
        x: cx + r * Math.cos(angle),
        y: cy + r * Math.sin(angle),
      }
    })
  }

  return (
    <svg viewBox="0 0 360 240" className="w-full h-60 rounded-xl bg-slate-900/1.5 border border-slate-200/60">
      {bonds.map((b, i) => {
        const p1 = coords[b.src]
        const p2 = coords[b.dst]
        if (!p1 || !p2) return null
        const isDouble = b.kind === 'double'
        const isArom = b.kind === 'aromatic'
        return (
          <line
            key={i}
            x1={p1.x}
            y1={p1.y}
            x2={p2.x}
            y2={p2.y}
            stroke={isDouble || isArom ? '#0d9488' : '#cbd5e1'}
            strokeWidth={isDouble ? 2.5 : 1.75}
            strokeDasharray={isArom ? '4 3' : undefined}
          />
        )
      })}

      {atoms.map((a, i) => {
        const p = coords[i]
        const isHetero = a.symbol !== 'C'
        const isArom = Boolean(a.aromatic)
        const chargeStr = a.charge > 0 ? `+${a.charge > 1 ? a.charge : ''}` : a.charge < 0 ? `-${Math.abs(a.charge) > 1 ? Math.abs(a.charge) : ''}` : ''
        return (
          <g key={i} transform={`translate(${p.x}, ${p.y})`}>
            <circle
              r={12.5}
              fill={isArom ? '#f0fdfa' : '#ffffff'}
              stroke={isHetero || a.charge !== 0 ? '#0d9488' : isArom ? '#14b8a6' : '#94a3b8'}
              strokeWidth={isArom || a.charge !== 0 ? 1.8 : 1.5}
              strokeDasharray={isArom ? '3 1.5' : undefined}
            />
            <text
              textAnchor="middle"
              dy="3.5"
              fontSize="9"
              fontWeight="600"
              fill={isHetero || a.charge !== 0 ? '#0f766e' : '#334155'}
            >
              {isArom && a.symbol === 'C' ? 'c' : a.symbol}{chargeStr}
              <tspan fontSize="6.5" dy="2" fill="#94a3b8">{i}</tspan>
            </text>
          </g>
        )
      })}
    </svg>
  )
}
