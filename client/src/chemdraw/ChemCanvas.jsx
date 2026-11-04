import React, { useState, useRef, useEffect, useCallback } from 'react'
import { ZoomIn, ZoomOut, Maximize2, Wand2, Sparkles } from 'lucide-react'
import {
  normalizeAtomLabel,
  preferredSproutAngle,
  buildRingTemplate,
  buildChainPoints,
} from './chemistryCore'

const BOND_LENGTH = 52
const SNAP_RADIUS = 18

export const ELEMENT_COLORS = {
  C: '#1a211e',
  N: '#2563eb',
  O: '#dc2626',
  S: '#ca8a04',
  P: '#ea580c',
  F: '#16a34a',
  Cl: '#16a34a',
  Br: '#991b1b',
  I: '#7e22ce',
  B: '#db2777',
  Si: '#475569',
  H: '#475569',
}

function pointInPolygon(pt, polygon) {
  let inside = false
  for (let i = 0, j = polygon.length - 1; i < polygon.length; j = i++) {
    const xi = polygon[i].x
    const yi = polygon[i].y
    const xj = polygon[j].x
    const yj = polygon[j].y
    const intersect =
      yi > pt.y !== yj > pt.y && pt.x < ((xj - xi) * (pt.y - yi)) / (yj - yi + 1e-9) + xi
    if (intersect) inside = !inside
  }
  return inside
}

// Render chemical formula text with automatic numeric subscripts (e.g. NH2 -> NH₂, CO2H -> CO₂H)
function renderSubscriptedLabel(text) {
  const parts = String(text).split(/(\d+)/g)
  return parts.map((part, idx) =>
    /^\d+$/.test(part) ? (
      <tspan key={idx} dy="3.5" fontSize="0.76em">
        {part}
      </tspan>
    ) : (
      <tspan key={idx} dy={idx > 0 && /^\d+$/.test(parts[idx - 1]) ? '-3.5' : '0'}>
        {part}
      </tspan>
    )
  )
}

function formatAtomDisplay(atom, state, degree, { showImplicitH, showCarbons }) {
  const raw = (atom.element || 'C').trim()
  const charge = atom.formalCharge || 0
  const radicals = atom.radicals || 0
  const isSkeletalCarbon =
    raw === 'C' &&
    !showCarbons &&
    charge === 0 &&
    radicals === 0 &&
    state?.valid !== false &&
    degree >= 1

  if (isSkeletalCarbon) return null

  const impH = showImplicitH ? state?.implicitH || 0 : 0
  const twoLetterElements = [
    'Cl', 'Br', 'Si', 'Na', 'Mg', 'Al', 'Ca', 'Fe', 'Zn', 'Pd', 'Pt', 'Au', 'Ag', 'Cu', 'Li', 'Se', 'Sn',
  ]
  const alreadySpellsH =
    raw.length > 1 && /[A-Z]/.test(raw) && !twoLetterElements.includes(raw)

  const hPart =
    !alreadySpellsH && raw !== 'C' && impH > 0
      ? `H${impH > 1 ? impH : ''}`
      : raw === 'C' && (degree === 0 || showCarbons) && impH > 0
        ? `H${impH > 1 ? impH : ''}`
        : ''

  const baseText = `${raw}${hPart}`
  const chargeText =
    charge === 0
      ? ''
      : charge === 1
        ? '⊕'
        : charge === -1
          ? '⊖'
          : `${Math.abs(charge)}${charge > 0 ? '+' : '−'}`
  const radText = radicals === 1 ? '•' : radicals >= 2 ? '••' : ''

  // Color by primary element symbol
  const primaryMatch = raw.match(/^(Cl|Br|Si|[A-Z])/)
  const colorKey = primaryMatch ? primaryMatch[1] : raw

  return {
    baseText,
    chargeText,
    radText,
    color: ELEMENT_COLORS[colorKey] || '#0f172a',
  }
}

export default function ChemCanvas({
  atoms,
  bonds,
  verification,
  activeTool,
  activeBondOrder,
  activeBondStereo,
  activeBondStyle,
  activeRing,
  activeElement,
  selectedAtomIds,
  onSelectAtomIds: onSelectAtomIdsProp,
  setSelectedAtomIds,
  styleSettings,
  onCommit: onCommitProp,
  onChange,
  highlightedAtomId = null,
  onLoadQuickStarter,
}) {
  const onCommit = onCommitProp || onChange || (() => {})
  const onSelectAtomIds = onSelectAtomIdsProp || setSelectedAtomIds || (() => {})

  const containerRef = useRef(null)
  const svgRef = useRef(null)
  const labelInputRef = useRef(null)
  const [viewSize, setViewSize] = useState({ w: 1060, h: 560 })
  const [zoom, setZoom] = useState(1)
  const [pan, setPan] = useState({ x: 0, y: 0 })
  const [spacePressed, setSpacePressed] = useState(false)
  const [hoveredAtomId, setHoveredAtomId] = useState(null)
  const [hoveredBondId, setHoveredBondId] = useState(null)
  const [cursorPt, setCursorPt] = useState(null)
  const [dragState, setDragState] = useState(null)
  const [editingAtom, setEditingAtom] = useState(null)

  const {
    lineWidthPx = 2,
    showImplicitH = true,
    showCarbons = false,
    fontSizePx = 15,
    bondSpacingPct = 18,
    showCrosshairs = true,
  } = styleSettings || {}

  // Track container dimensions 1:1 so the canvas fills the screen without distortion
  useEffect(() => {
    const el = containerRef.current
    if (!el) return
    const update = () => {
      const rect = el.getBoundingClientRect()
      if (rect.width > 100 && rect.height > 100) {
        setViewSize({ w: Math.round(rect.width), h: Math.round(rect.height) })
      }
    }
    update()
    const ro = new ResizeObserver(update)
    ro.observe(el)
    return () => ro.disconnect()
  }, [])

  // Fit and center molecule within the current viewport
  const handleFitView = useCallback(() => {
    if (!atoms.length) {
      setZoom(1)
      setPan({ x: 0, y: 0 })
      return
    }
    const xs = atoms.map((a) => a.x)
    const ys = atoms.map((a) => a.y)
    const minX = Math.min(...xs)
    const maxX = Math.max(...xs)
    const minY = Math.min(...ys)
    const maxY = Math.max(...ys)
    const molW = Math.max(maxX - minX, 80)
    const molH = Math.max(maxY - minY, 80)
    const pad = 110
    const availW = Math.max(viewSize.w - pad * 2, 200)
    const availH = Math.max(viewSize.h - pad * 2, 200)
    const nextZoom = Math.max(0.55, Math.min(1.35, Math.min(availW / molW, availH / molH)))
    const molCx = (minX + maxX) / 2
    const molCy = (minY + maxY) / 2
    setZoom(Math.round(nextZoom * 100) / 100)
    setPan({
      x: Math.round(viewSize.w / 2 - molCx * nextZoom),
      y: Math.round(viewSize.h / 2 - molCy * nextZoom),
    })
  }, [atoms, viewSize.w, viewSize.h])

  useEffect(() => {
    if (editingAtom && labelInputRef.current) {
      labelInputRef.current.focus()
      labelInputRef.current.select()
    }
  }, [editingAtom?.id])

  // Spacebar pan mode + keyboard shortcuts while hovering an atom or with selection active
  useEffect(() => {
    const onKeyDown = (e) => {
      if (editingAtom) return
      const tag = document.activeElement?.tagName
      if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT') return

      if (e.code === 'Space' && !spacePressed) {
        e.preventDefault()
        setSpacePressed(true)
        return
      }

      if ((e.key === 'Backspace' || e.key === 'Delete') && selectedAtomIds.size > 0) {
        e.preventDefault()
        const nextA = atoms.filter((a) => !selectedAtomIds.has(a.id))
        const nextB = bonds.filter(
          (b) => !selectedAtomIds.has(b.fromAtomId) && !selectedAtomIds.has(b.toAtomId)
        )
        onSelectAtomIds(new Set())
        onCommit(nextA, nextB)
        return
      }

      if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'a') {
        e.preventDefault()
        onSelectAtomIds(new Set(atoms.map((a) => a.id)))
        return
      }

      if (e.key === 'f' && !e.metaKey && !e.ctrlKey && !hoveredAtomId) {
        e.preventDefault()
        handleFitView()
        return
      }

      // Quick element typing or charge adjustment over a hovered atom
      if (!e.metaKey && !e.ctrlKey && !e.altKey && hoveredAtomId) {
        if (e.key === '+' || e.key === '=') {
          e.preventDefault()
          onCommit(
            atoms.map((a) =>
              a.id === hoveredAtomId
                ? { ...a, formalCharge: Math.min(4, (a.formalCharge || 0) + 1) }
                : a
            ),
            bonds
          )
          return
        }
        if (e.key === '-' || e.key === '_') {
          e.preventDefault()
          onCommit(
            atoms.map((a) =>
              a.id === hoveredAtomId
                ? { ...a, formalCharge: Math.max(-4, (a.formalCharge || 0) - 1) }
                : a
            ),
            bonds
          )
          return
        }
        const keyMap = {
          c: 'C',
          n: 'N',
          o: 'O',
          s: 'S',
          p: 'P',
          f: 'F',
          i: 'I',
          b: 'B',
          h: 'H',
        }
        const el = keyMap[e.key.toLowerCase()]
        if (el) {
          e.preventDefault()
          onCommit(
            atoms.map((a) => (a.id === hoveredAtomId ? { ...a, element: el } : a)),
            bonds
          )
        }
      }
    }
    const onKeyUp = (e) => {
      if (e.code === 'Space') setSpacePressed(false)
    }
    window.addEventListener('keydown', onKeyDown)
    window.addEventListener('keyup', onKeyUp)
    return () => {
      window.removeEventListener('keydown', onKeyDown)
      window.removeEventListener('keyup', onKeyUp)
    }
  }, [atoms, bonds, hoveredAtomId, selectedAtomIds, editingAtom, spacePressed, handleFitView])

  const atomById = new Map(atoms.map((a) => [a.id, a]))
  const degreeById = new Map(atoms.map((a) => [a.id, 0]))
  for (const b of bonds) {
    degreeById.set(b.fromAtomId, (degreeById.get(b.fromAtomId) || 0) + 1)
    degreeById.set(b.toAtomId, (degreeById.get(b.toAtomId) || 0) + 1)
  }

  const nextIds = (atomList, bondList) => {
    const maxA = atomList.reduce((m, a) => {
      const n = Number(String(a.id).replace(/\D+/g, ''))
      return Number.isFinite(n) ? Math.max(m, n) : m
    }, 0)
    const maxB = bondList.reduce((m, b) => {
      const n = Number(String(b.id).replace(/\D+/g, ''))
      return Number.isFinite(n) ? Math.max(m, n) : m
    }, 0)
    return { nextAtomNum: maxA + 1, nextBondNum: maxB + 1 }
  }

  // Convert screen pointer event to world coordinates (accounting for pan & zoom)
  const getSvgCoords = (e) => {
    const svg = svgRef.current
    if (!svg) return { x: 400, y: 260 }
    const rect = svg.getBoundingClientRect()
    const screenX = ((e.clientX - rect.left) * viewSize.w) / rect.width
    const screenY = ((e.clientY - rect.top) * viewSize.h) / rect.height
    return {
      x: Math.round(((screenX - pan.x) / zoom) * 10) / 10,
      y: Math.round(((screenY - pan.y) / zoom) * 10) / 10,
    }
  }

  const findNearestAtom = (pt, excludeId = null) => {
    let best = null
    let bestDist = SNAP_RADIUS
    for (const a of atoms) {
      if (a.id === excludeId) continue
      const d = Math.hypot(a.x - pt.x, a.y - pt.y)
      if (d <= bestDist) {
        bestDist = d
        best = a
      }
    }
    return best
  }

  const getConnectedComponent = (startAtomId) => {
    const visited = new Set([startAtomId])
    const queue = [startAtomId]
    while (queue.length > 0) {
      const cur = queue.shift()
      for (const b of bonds) {
        const other =
          b.fromAtomId === cur ? b.toAtomId : b.toAtomId === cur ? b.fromAtomId : null
        if (other && !visited.has(other)) {
          visited.add(other)
          queue.push(other)
        }
      }
    }
    return visited
  }

  const commitInlineLabel = () => {
    if (!editingAtom) return
    const raw = editingAtom.value.trim()
    setEditingAtom(null)
    if (!raw) return
    const norm = normalizeAtomLabel(raw)
    onCommit(
      atoms.map((a) => (a.id === editingAtom.id ? { ...a, element: norm } : a)),
      bonds
    )
  }

  const placeRing = ({ cx, cy, fuseBond = null, sproutAtom = null }) => {
    let { nextAtomNum, nextBondNum } = nextIds(atoms, bonds)
    if (fuseBond) {
      const tpl = buildRingTemplate(activeRing, { fuseBond, atoms, bondLength: BOND_LENGTH })
      if (!tpl.points.length) return
      const createdAtoms = []
      const ringVertexIds = [tpl.a1Id, tpl.a2Id]

      for (const pt of tpl.points) {
        const existing = findNearestAtom(pt)
        if (existing) {
          ringVertexIds.push(existing.id)
        } else {
          const id = `a${nextAtomNum++}`
          createdAtoms.push({
            id,
            element: pt.element || 'C',
            formalCharge: 0,
            x: pt.x,
            y: pt.y,
          })
          ringVertexIds.push(id)
        }
      }

      const nextBondList = [...bonds]
      for (let i = 1; i < ringVertexIds.length; i += 1) {
        const u = ringVertexIds[i]
        const v = ringVertexIds[(i + 1) % ringVertexIds.length]
        if (u === v) continue
        const exists = nextBondList.some(
          (b) => (b.fromAtomId === u && b.toAtomId === v) || (b.fromAtomId === v && b.toAtomId === u)
        )
        if (!exists) {
          nextBondList.push({
            id: `b${nextBondNum++}`,
            fromAtomId: u,
            toAtomId: v,
            order: tpl.orders[i] || 'single',
          })
        }
      }
      onCommit([...atoms, ...createdAtoms], nextBondList)
      return
    }

    let centerX = cx
    let centerY = cy
    if (sproutAtom) {
      const ang = preferredSproutAngle(sproutAtom, atoms, bonds, BOND_LENGTH)
      centerX = sproutAtom.x + Math.cos(ang) * (BOND_LENGTH * 1.45)
      centerY = sproutAtom.y + Math.sin(ang) * (BOND_LENGTH * 1.45)
    }

    const tpl = buildRingTemplate(activeRing, { cx: centerX, cy: centerY, bondLength: BOND_LENGTH })
    const newAtoms = tpl.points.map((pt) => ({
      id: `a${nextAtomNum++}`,
      element: pt.element || 'C',
      formalCharge: 0,
      x: pt.x,
      y: pt.y,
    }))
    const newBonds = newAtoms.map((a, idx) => ({
      id: `b${nextBondNum++}`,
      fromAtomId: a.id,
      toAtomId: newAtoms[(idx + 1) % newAtoms.length].id,
      order: tpl.orders[idx] || 'single',
    }))
    if (sproutAtom && newAtoms.length > 0) {
      newBonds.push({
        id: `b${nextBondNum++}`,
        fromAtomId: sproutAtom.id,
        toAtomId: newAtoms[0].id,
        order: 'single',
      })
    }
    onCommit([...atoms, ...newAtoms], [...bonds, ...newBonds])
  }

  const handleAtomPointerDown = (e, atom) => {
    e.stopPropagation()
    if (editingAtom) commitInlineLabel()

    if (spacePressed || e.button === 1) {
      setDragState({
        mode: 'pan_canvas',
        startClientX: e.clientX,
        startClientY: e.clientY,
        origPanX: pan.x,
        origPanY: pan.y,
      })
      return
    }

    if (activeTool === 'erase') {
      const nextA = atoms.filter((a) => a.id !== atom.id)
      const nextB = bonds.filter((b) => b.fromAtomId !== atom.id && b.toAtomId !== atom.id)
      onCommit(nextA, nextB)
      return
    }

    if (activeTool === 'select' || activeTool === 'lasso') {
      let nextSelected = new Set(selectedAtomIds)
      if (e.shiftKey) {
        if (nextSelected.has(atom.id)) nextSelected.delete(atom.id)
        else nextSelected.add(atom.id)
        onSelectAtomIds(nextSelected)
      } else if (!nextSelected.has(atom.id)) {
        nextSelected = getConnectedComponent(atom.id)
        onSelectAtomIds(nextSelected)
      }
      const pt = getSvgCoords(e)
      const snapshot = new Map(atoms.map((a) => [a.id, { x: a.x, y: a.y }]))
      setDragState({
        mode: 'move_selection',
        startX: pt.x,
        startY: pt.y,
        selectedIds: nextSelected,
        snapshot,
        moved: false,
      })
      return
    }

    if (activeTool === 'text') {
      setEditingAtom({
        id: atom.id,
        x: atom.x,
        y: atom.y,
        value: atom.element || 'C',
      })
      return
    }

    if (activeTool === 'charge_plus' || activeTool === 'charge_minus') {
      const delta = activeTool === 'charge_plus' ? 1 : -1
      onCommit(
        atoms.map((a) =>
          a.id === atom.id
            ? { ...a, formalCharge: Math.max(-4, Math.min(4, (a.formalCharge || 0) + delta)) }
            : a
        ),
        bonds
      )
      return
    }

    if (activeTool === 'radical' || activeTool === 'lone_pair') {
      const step = activeTool === 'lone_pair' ? 2 : 1
      onCommit(
        atoms.map((a) => (a.id === atom.id ? { ...a, radicals: ((a.radicals || 0) + step) % 3 } : a)),
        bonds
      )
      return
    }

    if (activeTool === 'ring') {
      placeRing({ cx: atom.x, cy: atom.y, sproutAtom: atom })
      return
    }

    if (activeTool === 'chain') {
      setDragState({
        mode: 'draw_chain',
        fromAtomId: atom.id,
        fromX: atom.x,
        fromY: atom.y,
        points: [
          { x: atom.x, y: atom.y },
          { x: atom.x + BOND_LENGTH * 0.86, y: atom.y - BOND_LENGTH * 0.5 },
        ],
      })
      return
    }

    if (activeTool === 'atom' || activeTool === 'bond') {
      const ang = preferredSproutAngle(atom, atoms, bonds, BOND_LENGTH)
      const targetX = Math.round((atom.x + Math.cos(ang) * BOND_LENGTH) * 10) / 10
      const targetY = Math.round((atom.y + Math.sin(ang) * BOND_LENGTH) * 10) / 10
      setDragState({
        mode: 'draw_bond',
        fromAtomId: atom.id,
        fromX: atom.x,
        fromY: atom.y,
        toX: targetX,
        toY: targetY,
        snapAtomId: null,
        moved: false,
        relabelOnClick: activeTool === 'atom',
      })
    }
  }

  const handleBondPointerDown = (e, bond) => {
    e.stopPropagation()
    if (editingAtom) commitInlineLabel()

    if (spacePressed || e.button === 1) {
      setDragState({
        mode: 'pan_canvas',
        startClientX: e.clientX,
        startClientY: e.clientY,
        origPanX: pan.x,
        origPanY: pan.y,
      })
      return
    }

    if (activeTool === 'erase') {
      onCommit(
        atoms,
        bonds.filter((b) => b.id !== bond.id)
      )
      return
    }

    if (activeTool === 'select' || activeTool === 'lasso') {
      let nextSelected = new Set(selectedAtomIds)
      if (!nextSelected.has(bond.fromAtomId) || !nextSelected.has(bond.toAtomId)) {
        nextSelected = getConnectedComponent(bond.fromAtomId)
        onSelectAtomIds(nextSelected)
      }
      const pt = getSvgCoords(e)
      const snapshot = new Map(atoms.map((a) => [a.id, { x: a.x, y: a.y }]))
      setDragState({
        mode: 'move_selection',
        startX: pt.x,
        startY: pt.y,
        selectedIds: nextSelected,
        snapshot,
        moved: false,
      })
      return
    }

    if (activeTool === 'ring') {
      placeRing({ fuseBond: bond })
      return
    }

    if (activeTool === 'bond' || activeTool === 'atom') {
      onCommit(
        atoms,
        bonds.map((b) => {
          if (b.id !== bond.id) return b
          if (activeBondStereo) {
            const nextStereo =
              b.stereo === activeBondStereo
                ? activeBondStereo === 'up'
                  ? 'up_rev'
                  : activeBondStereo === 'down'
                    ? 'down_rev'
                    : undefined
                : activeBondStereo
            return { ...b, order: 'single', stereo: nextStereo, style: undefined }
          }
          if (activeBondStyle) {
            const nextStyle = b.style === activeBondStyle ? undefined : activeBondStyle
            return { ...b, order: 'single', stereo: undefined, style: nextStyle }
          }
          const nextOrder =
            b.order === activeBondOrder && !b.stereo && !b.style
              ? b.order === 'single'
                ? 'double'
                : b.order === 'double'
                  ? 'triple'
                  : 'single'
              : activeBondOrder
          return { ...b, order: nextOrder, stereo: undefined, style: undefined }
        })
      )
    }
  }

  const handleCanvasPointerDown = (e) => {
    if (editingAtom) {
      commitInlineLabel()
      return
    }
    if (spacePressed || e.button === 1) {
      setDragState({
        mode: 'pan_canvas',
        startClientX: e.clientX,
        startClientY: e.clientY,
        origPanX: pan.x,
        origPanY: pan.y,
      })
      return
    }

    const pt = getSvgCoords(e)
    const hitAtom = findNearestAtom(pt)
    if (hitAtom) {
      handleAtomPointerDown(e, hitAtom)
      return
    }

    if (activeTool === 'select') {
      if (!e.shiftKey) onSelectAtomIds(new Set())
      setDragState({
        mode: 'marquee',
        startX: pt.x,
        startY: pt.y,
        curX: pt.x,
        curY: pt.y,
      })
      return
    }

    if (activeTool === 'lasso') {
      if (!e.shiftKey) onSelectAtomIds(new Set())
      setDragState({
        mode: 'lasso',
        points: [pt],
      })
      return
    }

    if (activeTool === 'ring') {
      placeRing({ cx: pt.x, cy: pt.y })
      return
    }

    if (activeTool === 'text') {
      const { nextAtomNum } = nextIds(atoms, bonds)
      const newId = `a${nextAtomNum}`
      const nextAtoms = [
        ...atoms,
        {
          id: newId,
          element: 'C',
          formalCharge: 0,
          x: pt.x,
          y: pt.y,
        },
      ]
      onCommit(nextAtoms, bonds)
      setEditingAtom({ id: newId, x: pt.x, y: pt.y, value: '' })
      return
    }

    if (activeTool === 'atom') {
      const toX = Math.round((pt.x + Math.cos(-Math.PI / 6) * BOND_LENGTH) * 10) / 10
      const toY = Math.round((pt.y + Math.sin(-Math.PI / 6) * BOND_LENGTH) * 10) / 10
      setDragState({
        mode: 'new_bond',
        fromX: pt.x,
        fromY: pt.y,
        toX,
        toY,
        snapAtomId: null,
        moved: false,
        singleAtomOnClick: true,
      })
      return
    }

    if (activeTool === 'chain') {
      setDragState({
        mode: 'draw_chain',
        fromAtomId: null,
        fromX: pt.x,
        fromY: pt.y,
        points: [
          { x: pt.x, y: pt.y },
          { x: pt.x + BOND_LENGTH * 0.86, y: pt.y - BOND_LENGTH * 0.5 },
        ],
      })
      return
    }

    if (activeTool === 'bond') {
      const toX = Math.round((pt.x + Math.cos(-Math.PI / 6) * BOND_LENGTH) * 10) / 10
      const toY = Math.round((pt.y + Math.sin(-Math.PI / 6) * BOND_LENGTH) * 10) / 10
      setDragState({
        mode: 'new_bond',
        fromX: pt.x,
        fromY: pt.y,
        toX,
        toY,
        snapAtomId: null,
        moved: false,
      })
    }
  }

  const handlePointerMove = (e) => {
    if (dragState?.mode === 'pan_canvas') {
      const dx = e.clientX - dragState.startClientX
      const dy = e.clientY - dragState.startClientY
      setPan({
        x: Math.round(dragState.origPanX + dx),
        y: Math.round(dragState.origPanY + dy),
      })
      return
    }

    const pt = getSvgCoords(e)
    setCursorPt(pt)
    if (!dragState) return

    if (dragState.mode === 'move_selection') {
      const dx = pt.x - dragState.startX
      const dy = pt.y - dragState.startY
      if (Math.hypot(dx, dy) < 2 && !dragState.moved) return
      const nextAtoms = atoms.map((a) => {
        if (!dragState.selectedIds.has(a.id)) return a
        const orig = dragState.snapshot.get(a.id)
        if (!orig) return a
        return {
          ...a,
          x: Math.round((orig.x + dx) * 10) / 10,
          y: Math.round((orig.y + dy) * 10) / 10,
        }
      })
      onCommit(nextAtoms, bonds, { recordHistory: false })
      setDragState((prev) => ({ ...prev, lastAtoms: nextAtoms, moved: true }))
      return
    }

    if (dragState.mode === 'rotate_selection') {
      const distFromHandle = Math.hypot(pt.x - dragState.startPtX, pt.y - dragState.startPtY)
      if (distFromHandle < 2.5 && !dragState.moved) return
      const angNow = Math.atan2(pt.y - dragState.cy, pt.x - dragState.cx)
      // Normalize angle delta to (-π, π] so crossing the 9-o'clock branch cut never jumps
      const rawDelta = Math.atan2(
        Math.sin(angNow - dragState.startAngle),
        Math.cos(angNow - dragState.startAngle)
      )
      const delta = e.shiftKey
        ? Math.round(rawDelta / (Math.PI / 12)) * (Math.PI / 12)
        : rawDelta
      const cos = Math.cos(delta)
      const sin = Math.sin(delta)
      const nextAtoms = atoms.map((a) => {
        if (!dragState.selectedIds.has(a.id)) return a
        const orig = dragState.snapshot.get(a.id)
        if (!orig) return a
        const rx = orig.x - dragState.cx
        const ry = orig.y - dragState.cy
        return {
          ...a,
          x: Math.round((dragState.cx + rx * cos - ry * sin) * 10) / 10,
          y: Math.round((dragState.cy + rx * sin + ry * cos) * 10) / 10,
        }
      })
      onCommit(nextAtoms, bonds, { recordHistory: false })
      setDragState((prev) => ({
        ...prev,
        degrees: Math.round((delta * 180) / Math.PI),
        curX: pt.x,
        curY: pt.y,
        lastAtoms: nextAtoms,
        moved: true,
      }))
      return
    }

    if (dragState.mode === 'flip_selection') {
      const dx = pt.x - dragState.startX
      if (Math.abs(dx) < 6 && !dragState.moved) return
      // Rigid horizontal mirror (-1 or +1 only — never squash bond lengths)
      const scaleX = dx < -10 || (dx > 10 && pt.x < dragState.cx) ? -1 : -1
      const nextAtoms = atoms.map((a) => {
        if (!dragState.selectedIds.has(a.id)) return a
        const orig = dragState.snapshot.get(a.id)
        if (!orig) return a
        return {
          ...a,
          x: Math.round((dragState.cx + (orig.x - dragState.cx) * scaleX) * 10) / 10,
          y: orig.y,
        }
      })
      onCommit(nextAtoms, bonds, { recordHistory: false })
      setDragState((prev) => ({
        ...prev,
        lastAtoms: nextAtoms,
        moved: true,
      }))
      return
    }

    if (dragState.mode === 'marquee') {
      const minX = Math.min(dragState.startX, pt.x)
      const maxX = Math.max(dragState.startX, pt.x)
      const minY = Math.min(dragState.startY, pt.y)
      const maxY = Math.max(dragState.startY, pt.y)
      const hit = new Set(
        atoms
          .filter((a) => a.x >= minX && a.x <= maxX && a.y >= minY && a.y <= maxY)
          .map((a) => a.id)
      )
      onSelectAtomIds(hit)
      setDragState((prev) => ({ ...prev, curX: pt.x, curY: pt.y }))
      return
    }

    if (dragState.mode === 'lasso') {
      const nextPts = [...dragState.points, pt]
      if (nextPts.length >= 3) {
        const hit = new Set(atoms.filter((a) => pointInPolygon(a, nextPts)).map((a) => a.id))
        onSelectAtomIds(hit)
      }
      setDragState((prev) => ({ ...prev, points: nextPts }))
      return
    }

    if (dragState.mode === 'draw_chain') {
      const pts = buildChainPoints({ x: dragState.fromX, y: dragState.fromY }, pt, BOND_LENGTH)
      setDragState((prev) => ({ ...prev, points: pts }))
      return
    }

    const dx = pt.x - dragState.fromX
    const dy = pt.y - dragState.fromY
    const dist = Math.hypot(dx, dy)
    if (dist < 10 && !dragState.moved) return

    const snapTarget = findNearestAtom(pt, dragState.fromAtomId)
    if (snapTarget) {
      setDragState((prev) => ({
        ...prev,
        toX: snapTarget.x,
        toY: snapTarget.y,
        snapAtomId: snapTarget.id,
        moved: true,
      }))
      return
    }

    const rawAngle = Math.atan2(dy, dx)
    const step = Math.PI / 6
    const snappedAngle = Math.round(rawAngle / step) * step
    const toX = Math.round((dragState.fromX + Math.cos(snappedAngle) * BOND_LENGTH) * 10) / 10
    const toY = Math.round((dragState.fromY + Math.sin(snappedAngle) * BOND_LENGTH) * 10) / 10
    setDragState((prev) => ({
      ...prev,
      toX,
      toY,
      snapAtomId: null,
      moved: true,
    }))
  }

  const handlePointerUp = (e) => {
    if (!dragState) return
    const state = dragState
    if (state.pointerId != null) {
      try {
        svgRef.current?.releasePointerCapture?.(state.pointerId)
      } catch {
        // ignore if pointer capture was already released
      }
    }
    setDragState(null)

    if (state.mode === 'pan_canvas') return

    if (
      state.mode === 'move_selection' ||
      state.mode === 'rotate_selection' ||
      state.mode === 'flip_selection'
    ) {
      if (state.moved) {
        onCommit(state.lastAtoms || atoms, bonds)
        return
      }
      // Single click on [↻] handle rotates by 30° clockwise around selection center
      if (state.mode === 'rotate_selection') {
        const step = Math.PI / 6
        const cos = Math.cos(step)
        const sin = Math.sin(step)
        const nextAtoms = atoms.map((a) => {
          if (!state.selectedIds.has(a.id)) return a
          const orig = state.snapshot.get(a.id) || a
          const rx = orig.x - state.cx
          const ry = orig.y - state.cy
          return {
            ...a,
            x: Math.round((state.cx + rx * cos - ry * sin) * 10) / 10,
            y: Math.round((state.cy + rx * sin + ry * cos) * 10) / 10,
          }
        })
        onCommit(nextAtoms, bonds)
        return
      }
      // Single click on [↷] handle mirrors horizontally around selection center
      if (state.mode === 'flip_selection') {
        const nextAtoms = atoms.map((a) => {
          if (!state.selectedIds.has(a.id)) return a
          const orig = state.snapshot.get(a.id) || a
          return {
            ...a,
            x: Math.round((2 * state.cx - orig.x) * 10) / 10,
            y: orig.y,
          }
        })
        onCommit(nextAtoms, bonds)
      }
      return
    }

    if (state.mode === 'marquee' || state.mode === 'lasso') {
      return
    }

    if (state.mode === 'draw_chain') {
      const pts = state.points || []
      if (pts.length < 2) return
      let { nextAtomNum, nextBondNum } = nextIds(atoms, bonds)
      const nextAtoms = [...atoms]
      const nextBonds = [...bonds]
      let prevId = state.fromAtomId
      if (!prevId) {
        prevId = `a${nextAtomNum++}`
        nextAtoms.push({
          id: prevId,
          element: 'C',
          formalCharge: 0,
          x: pts[0].x,
          y: pts[0].y,
        })
      }
      for (let i = 1; i < pts.length; i += 1) {
        const pt = pts[i]
        const existing = findNearestAtom(pt, prevId)
        let curId = existing?.id
        if (!curId) {
          curId = `a${nextAtomNum++}`
          nextAtoms.push({
            id: curId,
            element: 'C',
            formalCharge: 0,
            x: pt.x,
            y: pt.y,
          })
        }
        if (
          curId !== prevId &&
          !nextBonds.some(
            (b) =>
              (b.fromAtomId === prevId && b.toAtomId === curId) ||
              (b.fromAtomId === curId && b.toAtomId === prevId)
          )
        ) {
          nextBonds.push({
            id: `b${nextBondNum++}`,
            fromAtomId: prevId,
            toAtomId: curId,
            order: 'single',
          })
        }
        prevId = curId
      }
      onCommit(nextAtoms, nextBonds)
      return
    }

    if (state.mode === 'new_bond' && state.singleAtomOnClick && !state.moved) {
      const { nextAtomNum } = nextIds(atoms, bonds)
      const norm = normalizeAtomLabel(activeElement || 'C')
      onCommit(
        [
          ...atoms,
          {
            id: `a${nextAtomNum}`,
            element: norm,
            formalCharge: 0,
            x: state.fromX,
            y: state.fromY,
          },
        ],
        bonds
      )
      return
    }

    // If clicked an existing atom in 'atom' mode without dragging, relabel if different; otherwise sprout
    if (state.mode === 'draw_bond' && state.relabelOnClick && !state.moved && state.fromAtomId) {
      const norm = normalizeAtomLabel(activeElement || 'C')
      const clickedAtom = atomById.get(state.fromAtomId)
      if (clickedAtom && clickedAtom.element !== norm) {
        onCommit(
          atoms.map((a) => (a.id === state.fromAtomId ? { ...a, element: norm } : a)),
          bonds
        )
        return
      }
    }

    const sproutElem = normalizeAtomLabel(activeElement || 'C')
    let { nextAtomNum, nextBondNum } = nextIds(atoms, bonds)
    const nextAtoms = [...atoms]
    const nextBonds = [...bonds]

    let fromId = state.fromAtomId
    if (!fromId) {
      fromId = `a${nextAtomNum++}`
      nextAtoms.push({
        id: fromId,
        element: 'C',
        formalCharge: 0,
        x: state.fromX,
        y: state.fromY,
      })
    }

    let toId = state.snapAtomId
    if (!toId) {
      const existingNear = findNearestAtom({ x: state.toX, y: state.toY }, fromId)
      if (existingNear) {
        toId = existingNear.id
      } else {
        toId = `a${nextAtomNum++}`
        nextAtoms.push({
          id: toId,
          element: sproutElem,
          formalCharge: 0,
          x: state.toX,
          y: state.toY,
        })
      }
    }

    if (fromId === toId) return

    const existingBondIdx = nextBonds.findIndex(
      (b) =>
        (b.fromAtomId === fromId && b.toAtomId === toId) ||
        (b.fromAtomId === toId && b.toAtomId === fromId)
    )
    if (existingBondIdx >= 0) {
      const cur = nextBonds[existingBondIdx]
      nextBonds[existingBondIdx] = {
        ...cur,
        order: activeBondStereo || activeBondStyle ? 'single' : activeBondOrder,
        stereo: activeBondStereo || undefined,
        style: activeBondStyle || undefined,
      }
    } else {
      nextBonds.push({
        id: `b${nextBondNum++}`,
        fromAtomId: fromId,
        toAtomId: toId,
        order: activeBondStereo || activeBondStyle ? 'single' : activeBondOrder,
        ...(activeBondStereo ? { stereo: activeBondStereo } : {}),
        ...(activeBondStyle ? { style: activeBondStyle } : {}),
      })
    }

    onCommit(nextAtoms, nextBonds)
  }

  const selectedAtoms = atoms.filter((a) => selectedAtomIds.has(a.id))
  const selectionBounds =
    selectedAtoms.length > 0
      ? {
          minX: Math.min(...selectedAtoms.map((a) => a.x)) - 22,
          maxX: Math.max(...selectedAtoms.map((a) => a.x)) + 22,
          minY: Math.min(...selectedAtoms.map((a) => a.y)) - 22,
          maxY: Math.max(...selectedAtoms.map((a) => a.y)) + 22,
        }
      : null

  const startRotateHandleDrag = (e) => {
    e.stopPropagation()
    if (!selectionBounds) return
    try {
      svgRef.current?.setPointerCapture?.(e.pointerId)
    } catch {
      // ignore if pointer capture is unavailable
    }
    const pt = getSvgCoords(e)
    const cx = (selectionBounds.minX + selectionBounds.maxX) / 2
    const cy = (selectionBounds.minY + selectionBounds.maxY) / 2
    const snapshot = new Map(atoms.map((a) => [a.id, { x: a.x, y: a.y }]))
    setDragState({
      mode: 'rotate_selection',
      pointerId: e.pointerId,
      cx,
      cy,
      initialBounds: { ...selectionBounds },
      startPtX: pt.x,
      startPtY: pt.y,
      curX: pt.x,
      curY: pt.y,
      startAngle: Math.atan2(pt.y - cy, pt.x - cx),
      selectedIds: new Set(selectedAtomIds),
      snapshot,
      degrees: 0,
      moved: false,
    })
  }

  const startTilt3DHandleDrag = (e) => {
    e.stopPropagation()
    if (!selectionBounds) return
    try {
      svgRef.current?.setPointerCapture?.(e.pointerId)
    } catch {
      // ignore if pointer capture is unavailable
    }
    const pt = getSvgCoords(e)
    const cx = (selectionBounds.minX + selectionBounds.maxX) / 2
    const cy = (selectionBounds.minY + selectionBounds.maxY) / 2
    const snapshot = new Map(atoms.map((a) => [a.id, { x: a.x, y: a.y }]))
    setDragState({
      mode: 'flip_selection',
      pointerId: e.pointerId,
      cx,
      cy,
      startX: pt.x,
      selectedIds: new Set(selectedAtomIds),
      snapshot,
      degrees: 0,
      moved: false,
    })
  }

  const ringGhost =
    activeTool === 'ring' && cursorPt && !dragState
      ? (() => {
          const hoveredBond = hoveredBondId ? bonds.find((b) => b.id === hoveredBondId) : null
          if (hoveredBond) {
            const tpl = buildRingTemplate(activeRing, {
              fuseBond: hoveredBond,
              atoms,
              bondLength: BOND_LENGTH,
            })
            const a1 = atomById.get(hoveredBond.fromAtomId)
            const a2 = atomById.get(hoveredBond.toAtomId)
            return a1 && a2 ? { points: [a1, a2, ...tpl.points] } : null
          }
          const hoveredAtom = hoveredAtomId ? atomById.get(hoveredAtomId) : null
          if (hoveredAtom) {
            const ang = preferredSproutAngle(hoveredAtom, atoms, bonds, BOND_LENGTH)
            const cx = hoveredAtom.x + Math.cos(ang) * (BOND_LENGTH * 1.45)
            const cy = hoveredAtom.y + Math.sin(ang) * (BOND_LENGTH * 1.45)
            return buildRingTemplate(activeRing, { cx, cy, bondLength: BOND_LENGTH })
          }
          return buildRingTemplate(activeRing, {
            cx: cursorPt.x,
            cy: cursorPt.y,
            bondLength: BOND_LENGTH,
          })
        })()
      : null

  const sproutPreview =
    (activeTool === 'bond' || activeTool === 'atom') && hoveredAtomId && !dragState
      ? (() => {
          const atom = atomById.get(hoveredAtomId)
          if (!atom) return null
          const ang = preferredSproutAngle(atom, atoms, bonds, BOND_LENGTH)
          return {
            x1: atom.x,
            y1: atom.y,
            x2: atom.x + Math.cos(ang) * BOND_LENGTH,
            y2: atom.y + Math.sin(ang) * BOND_LENGTH,
          }
        })()
      : null

  const doubleBondOffset = Math.max(2.4, (BOND_LENGTH * Number(bondSpacingPct || 18)) / 270)
  const axisX = Math.round(viewSize.w * 0.72)
  const axisY = Math.round(viewSize.h * 0.78)
  const inspectedAtomId = hoveredAtomId || highlightedAtomId
  const inspectedAtom = inspectedAtomId ? atomById.get(inspectedAtomId) : null
  const inspectedState = inspectedAtomId ? verification?.atomStateById?.get(inspectedAtomId) : null

  return (
    <div
      ref={containerRef}
      className="relative flex-1 min-w-0 bg-white overflow-hidden select-none h-[calc(100vh-275px)] min-h-[500px] max-h-[700px]"
    >
      <svg
        ref={svgRef}
        viewBox={`0 0 ${viewSize.w} ${viewSize.h}`}
        className={`w-full h-full block touch-none ${
          spacePressed || dragState?.mode === 'pan_canvas'
            ? 'cursor-grab active:cursor-grabbing'
            : activeTool === 'select' || activeTool === 'lasso'
              ? 'cursor-default'
              : activeTool === 'text'
                ? 'cursor-text'
                : 'cursor-crosshair'
        }`}
        onPointerDown={handleCanvasPointerDown}
        onPointerMove={handlePointerMove}
        onPointerUp={handlePointerUp}
        onPointerLeave={() => setCursorPt(null)}
      >
        <defs>
          <pattern id="cd-page-grid" width="28" height="28" patternUnits="userSpaceOnUse">
            <path
              d="M 28 0 L 0 0 0 28"
              fill="none"
              stroke="rgba(101, 111, 120, 0.12)"
              strokeWidth="1"
            />
          </pattern>
          <marker
            id="cd-dative-arrow"
            viewBox="0 0 10 10"
            refX="8"
            refY="5"
            markerWidth="6"
            markerHeight="6"
            orient="auto-start-reverse"
          >
            <path d="M 0 1 L 10 5 L 0 9 z" fill="#20242a" />
          </marker>
        </defs>

        {/* Page Grid Background */}
        <rect width={viewSize.w} height={viewSize.h} fill="url(#cd-page-grid)" />

        {/* ChemDraft Crosshair Coordinate Axes with Tick Marks */}
        {showCrosshairs && (
          <g className="pointer-events-none" opacity="0.65">
            <line x1={0} y1={axisY} x2={viewSize.w} y2={axisY} stroke="#334155" strokeWidth="1" />
            <line x1={axisX} y1={0} x2={axisX} y2={viewSize.h} stroke="#334155" strokeWidth="1" />
            {Array.from({ length: Math.ceil(viewSize.w / 14) }, (_, i) => {
              const x = i * 14
              const isMajor = i % 4 === 0
              const isHalf = i % 2 === 0
              const h = isMajor ? 5 : isHalf ? 3.2 : 2
              return (
                <line
                  key={`hx-${i}`}
                  x1={x}
                  y1={axisY - h}
                  x2={x}
                  y2={axisY + h}
                  stroke="#334155"
                  strokeWidth="1"
                />
              )
            })}
            {Array.from({ length: Math.ceil(viewSize.h / 14) }, (_, i) => {
              const y = i * 14
              const isMajor = i % 4 === 0
              const isHalf = i % 2 === 0
              const w = isMajor ? 5 : isHalf ? 3.2 : 2
              return (
                <line
                  key={`vy-${i}`}
                  x1={axisX - w}
                  y1={y}
                  x2={axisX + w}
                  y2={y}
                  stroke="#334155"
                  strokeWidth="1"
                />
              )
            })}
          </g>
        )}

        {/* World Pan & Zoom Group */}
        <g transform={`translate(${pan.x}, ${pan.y}) scale(${zoom})`}>
          {/* ChemDraft Green Selection Blob */}
          {selectedAtomIds.size > 0 && (
            <g className="pointer-events-none" opacity="0.24" color="#1d7f68">
              {bonds
                .filter(
                  (b) => selectedAtomIds.has(b.fromAtomId) && selectedAtomIds.has(b.toAtomId)
                )
                .map((b) => {
                  const a1 = atomById.get(b.fromAtomId)
                  const a2 = atomById.get(b.toAtomId)
                  if (!a1 || !a2) return null
                  return (
                    <line
                      key={`sel-bond-${b.id}`}
                      x1={a1.x}
                      y1={a1.y}
                      x2={a2.x}
                      y2={a2.y}
                      stroke="#1d7f68"
                      strokeWidth="19"
                      strokeLinecap="round"
                    />
                  )
                })}
              {selectedAtoms.map((a) => (
                <circle
                  key={`sel-atom-${a.id}`}
                  cx={a.x}
                  cy={a.y}
                  r="11.5"
                  fill="#1d7f68"
                  stroke="#145e4d"
                  strokeWidth="1.2"
                />
              ))}
            </g>
          )}

          {/* Selection Frame: 4 Green Corner Brackets (┌ ┐ └ ┘) + Floating [↻] [↷] Handles */}
          {selectionBounds &&
            (() => {
              const isRotating =
                dragState?.mode === 'rotate_selection' && dragState.initialBounds
              const activeBounds = isRotating ? dragState.initialBounds : selectionBounds
              const midX = (activeBounds.minX + activeBounds.maxX) / 2
              const midY = (activeBounds.minY + activeBounds.maxY) / 2
              // Place handles at the bottom if the top of the selection is close to the top of the viewport
              const placeBottom = activeBounds.minY * zoom + pan.y < 52
              const handleY = placeBottom ? activeBounds.maxY + 26 : activeBounds.minY - 26
              const stemY1 = placeBottom ? -12.5 : 12.5
              const stemY2 = placeBottom ? -23 : 23

              return (
                <>
                  {/* Rotation Pivot Crosshair + Radius Guide Line during active rotation */}
                  {isRotating && (
                    <g className="pointer-events-none">
                      <line
                        x1={dragState.cx}
                        y1={dragState.cy}
                        x2={dragState.curX ?? dragState.startPtX}
                        y2={dragState.curY ?? dragState.startPtY}
                        stroke="#1d7f68"
                        strokeWidth="1.2"
                        strokeDasharray="4 3"
                        opacity="0.7"
                      />
                      <circle
                        cx={dragState.cx}
                        cy={dragState.cy}
                        r="4.5"
                        fill="#ffffff"
                        stroke="#1d7f68"
                        strokeWidth="1.6"
                      />
                      <line
                        x1={dragState.cx - 8}
                        y1={dragState.cy}
                        x2={dragState.cx + 8}
                        y2={dragState.cy}
                        stroke="#1d7f68"
                        strokeWidth="1.3"
                      />
                      <line
                        x1={dragState.cx}
                        y1={dragState.cy - 8}
                        x2={dragState.cx}
                        y2={dragState.cy + 8}
                        stroke="#1d7f68"
                        strokeWidth="1.3"
                      />
                    </g>
                  )}

                  <g
                    transform={
                      isRotating
                        ? `rotate(${dragState.degrees || 0}, ${dragState.cx}, ${dragState.cy})`
                        : undefined
                    }
                  >
                    <path
                      d={`M ${activeBounds.minX} ${activeBounds.minY + 12} L ${activeBounds.minX} ${activeBounds.minY} L ${activeBounds.minX + 12} ${activeBounds.minY}`}
                      fill="none"
                      stroke="#1d7f68"
                      strokeWidth="2.2"
                    />
                    <path
                      d={`M ${activeBounds.maxX - 12} ${activeBounds.minY} L ${activeBounds.maxX} ${activeBounds.minY} L ${activeBounds.maxX} ${activeBounds.minY + 12}`}
                      fill="none"
                      stroke="#1d7f68"
                      strokeWidth="2.2"
                    />
                    <path
                      d={`M ${activeBounds.minX} ${activeBounds.maxY - 12} L ${activeBounds.minX} ${activeBounds.maxY} L ${activeBounds.minX + 12} ${activeBounds.maxY}`}
                      fill="none"
                      stroke="#1d7f68"
                      strokeWidth="2.2"
                    />
                    <path
                      d={`M ${activeBounds.maxX - 12} ${activeBounds.maxY} L ${activeBounds.maxX} ${activeBounds.maxY} L ${activeBounds.maxX} ${activeBounds.maxY - 12}`}
                      fill="none"
                      stroke="#1d7f68"
                      strokeWidth="2.2"
                    />

                    {/* Rotate 2D Handle */}
                    <g
                      transform={`translate(${midX - 16}, ${handleY})`}
                      className="cursor-grab active:cursor-grabbing"
                      onPointerDown={startRotateHandleDrag}
                    >
                      <title>
                        Drag in a circle to rotate selection (hold Shift for 15° snap, or click to rotate 30°)
                      </title>
                      <line
                        x1="0"
                        y1={stemY1}
                        x2="0"
                        y2={stemY2}
                        stroke="#1d7f68"
                        strokeWidth="1.5"
                      />
                      <rect
                        x="-12"
                        y="-12"
                        width="24"
                        height="24"
                        rx="4"
                        fill="#ffffff"
                        stroke="#2d8a72"
                        strokeWidth="1.5"
                      />
                      <g
                        transform="translate(-12, -12)"
                        fill="none"
                        stroke="#1d7f68"
                        strokeWidth="1.9"
                        strokeLinecap="round"
                        strokeLinejoin="round"
                      >
                        <path d="M7 8.9a6.9 6.9 0 0 1 10.2-1.3" />
                        <path d="M17.4 4.6l0.4 4.1-4.1-0.3" />
                        <path d="M17 15.1a6.9 6.9 0 0 1-10.2 1.3" />
                        <path d="M6.6 19.4l-0.4-4.1 4.1 0.3" />
                      </g>
                    </g>

                    {/* Rigid Horizontal Flip / Mirror Handle */}
                    <g
                      transform={`translate(${midX + 16}, ${handleY})`}
                      className="cursor-pointer"
                      onPointerDown={startTilt3DHandleDrag}
                    >
                      <title>Click or drag horizontally to flip / mirror selection</title>
                      <line
                        x1="0"
                        y1={stemY1}
                        x2="0"
                        y2={stemY2}
                        stroke="#1d7f68"
                        strokeWidth="1.5"
                      />
                      <rect
                        x="-12"
                        y="-12"
                        width="24"
                        height="24"
                        rx="4"
                        fill="#ffffff"
                        stroke="#2d8a72"
                        strokeWidth="1.5"
                      />
                      <g transform="translate(-12, -12)">
                        <path
                          d="M4.2 12.4c0-4.1 4-7.2 9-7.2 4.7 0 8.4 2.8 8.6 6.7"
                          fill="none"
                          stroke="#1d7f68"
                          strokeWidth="2.2"
                          strokeLinecap="round"
                        />
                        <path
                          d="M4.7 14.1c1.4 2.9 4.7 4.7 8.7 4.7"
                          fill="none"
                          stroke="#1d7f68"
                          strokeWidth="2.2"
                          strokeLinecap="round"
                        />
                        <path d="M11.2 10.6l7.2 5.5-7.2 5.5v-3.7H7.9v-3.6h3.3z" fill="#1d7f68" />
                      </g>
                    </g>
                  </g>

                  {/* Upright Angle Badge at Pivot while Rotating */}
                  {isRotating && (
                    <g
                      transform={`translate(${midX}, ${midY - 22})`}
                      className="pointer-events-none"
                    >
                      <rect
                        x="-24"
                        y="-10"
                        width="48"
                        height="19"
                        rx="4"
                        fill="#ffffff"
                        stroke="#1d7f68"
                        strokeWidth="1.4"
                      />
                      <text
                        x="0"
                        y="0.5"
                        textAnchor="middle"
                        dominantBaseline="central"
                        fontSize="10.5"
                        fontWeight="700"
                        fill="#124e40"
                      >
                        {dragState.degrees > 0 ? `+${dragState.degrees}°` : `${dragState.degrees}°`}
                      </text>
                    </g>
                  )}
                </>
              )
            })()}

          {/* Render Bonds */}
          {bonds.map((bond) => {
            const a1 = atomById.get(bond.fromAtomId)
            const a2 = atomById.get(bond.toAtomId)
            if (!a1 || !a2) return null
            const dx = a2.x - a1.x
            const dy = a2.y - a1.y
            const len = Math.hypot(dx, dy) || 1
            const nx = -dy / len
            const ny = dx / len
            const isHovered = hoveredBondId === bond.id
            const isEraseHover = isHovered && activeTool === 'erase'
            const hasUnresolvedAtom =
              verification?.resolution?.unresolvedAtomIds?.has(a1.id) &&
              verification?.resolution?.unresolvedAtomIds?.has(a2.id)
            const stroke = isEraseHover
              ? '#b3261e'
              : hasUnresolvedAtom
                ? '#b3261e'
                : '#1a211e'
            const sw = Number(lineWidthPx) || 2

            const startPt = bond.stereo?.endsWith('_rev') ? a2 : a1
            const endPt = bond.stereo?.endsWith('_rev') ? a1 : a2
            const sdx = endPt.x - startPt.x
            const sdy = endPt.y - startPt.y

            return (
              <g
                key={bond.id}
                className="cursor-pointer"
                onMouseEnter={() => setHoveredBondId(bond.id)}
                onMouseLeave={() => setHoveredBondId(null)}
                onPointerDown={(e) => handleBondPointerDown(e, bond)}
              >
                <line x1={a1.x} y1={a1.y} x2={a2.x} y2={a2.y} stroke="transparent" strokeWidth={16} />

                {isHovered && (
                  <line
                    x1={a1.x}
                    y1={a1.y}
                    x2={a2.x}
                    y2={a2.y}
                    stroke={isEraseHover ? '#fde8e7' : 'rgba(29, 127, 104, 0.25)'}
                    strokeWidth={10}
                    strokeLinecap="round"
                  />
                )}

                {bond.stereo === 'up' || bond.stereo === 'up_rev' ? (
                  <polygon
                    points={`${startPt.x},${startPt.y} ${endPt.x + nx * 5.2},${endPt.y + ny * 5.2} ${endPt.x - nx * 5.2},${endPt.y - ny * 5.2}`}
                    fill={stroke}
                  />
                ) : bond.stereo === 'down' || bond.stereo === 'down_rev' ? (
                  Array.from({ length: 6 }, (_, i) => {
                    const t = (i + 1) / 6
                    const cx = startPt.x + sdx * t
                    const cy = startPt.y + sdy * t
                    const hw = 5 * t
                    return (
                      <line
                        key={i}
                        x1={cx - nx * hw}
                        y1={cy - ny * hw}
                        x2={cx + nx * hw}
                        y2={cy + ny * hw}
                        stroke={stroke}
                        strokeWidth={Math.max(1.5, sw * 0.85)}
                      />
                    )
                  })
                ) : bond.style === 'dashed' ? (
                  <line
                    x1={a1.x}
                    y1={a1.y}
                    x2={a2.x}
                    y2={a2.y}
                    stroke={stroke}
                    strokeWidth={sw}
                    strokeDasharray="5 4"
                    strokeLinecap="round"
                  />
                ) : bond.style === 'bold' ? (
                  <line
                    x1={a1.x}
                    y1={a1.y}
                    x2={a2.x}
                    y2={a2.y}
                    stroke={stroke}
                    strokeWidth={sw * 2.3}
                    strokeLinecap="butt"
                  />
                ) : bond.order === 'double' ? (
                  <>
                    <line
                      x1={a1.x + nx * doubleBondOffset}
                      y1={a1.y + ny * doubleBondOffset}
                      x2={a2.x + nx * doubleBondOffset}
                      y2={a2.y + ny * doubleBondOffset}
                      stroke={stroke}
                      strokeWidth={sw}
                      strokeLinecap="round"
                    />
                    <line
                      x1={a1.x - nx * doubleBondOffset}
                      y1={a1.y - ny * doubleBondOffset}
                      x2={a2.x - nx * doubleBondOffset}
                      y2={a2.y - ny * doubleBondOffset}
                      stroke={stroke}
                      strokeWidth={sw}
                      strokeLinecap="round"
                    />
                  </>
                ) : bond.order === 'triple' ? (
                  <>
                    <line
                      x1={a1.x}
                      y1={a1.y}
                      x2={a2.x}
                      y2={a2.y}
                      stroke={stroke}
                      strokeWidth={sw}
                      strokeLinecap="round"
                    />
                    <line
                      x1={a1.x + nx * (doubleBondOffset * 1.35)}
                      y1={a1.y + ny * (doubleBondOffset * 1.35)}
                      x2={a2.x + nx * (doubleBondOffset * 1.35)}
                      y2={a2.y + ny * (doubleBondOffset * 1.35)}
                      stroke={stroke}
                      strokeWidth={sw * 0.9}
                      strokeLinecap="round"
                    />
                    <line
                      x1={a1.x - nx * (doubleBondOffset * 1.35)}
                      y1={a1.y - ny * (doubleBondOffset * 1.35)}
                      x2={a2.x - nx * (doubleBondOffset * 1.35)}
                      y2={a2.y - ny * (doubleBondOffset * 1.35)}
                      stroke={stroke}
                      strokeWidth={sw * 0.9}
                      strokeLinecap="round"
                    />
                  </>
                ) : bond.order === 'aromatic' ? (
                  <>
                    <line
                      x1={a1.x}
                      y1={a1.y}
                      x2={a2.x}
                      y2={a2.y}
                      stroke={stroke}
                      strokeWidth={sw}
                      strokeLinecap="round"
                    />
                    <line
                      x1={a1.x + dx * 0.14 + nx * (doubleBondOffset * 1.1)}
                      y1={a1.y + dy * 0.14 + ny * (doubleBondOffset * 1.1)}
                      x2={a2.x - dx * 0.14 + nx * (doubleBondOffset * 1.1)}
                      y2={a2.y - dy * 0.14 + ny * (doubleBondOffset * 1.1)}
                      stroke={hasUnresolvedAtom ? '#b3261e' : '#1d7f68'}
                      strokeWidth={sw * 0.9}
                      strokeDasharray="3.5 3"
                      strokeLinecap="round"
                    />
                  </>
                ) : bond.order === 'dative' ? (
                  <line
                    x1={a1.x}
                    y1={a1.y}
                    x2={a2.x - (dx / len) * 10}
                    y2={a2.y - (dy / len) * 10}
                    stroke={stroke}
                    strokeWidth={sw}
                    strokeDasharray="4 3"
                    markerEnd="url(#cd-dative-arrow)"
                  />
                ) : (
                  <line
                    x1={a1.x}
                    y1={a1.y}
                    x2={a2.x}
                    y2={a2.y}
                    stroke={stroke}
                    strokeWidth={sw}
                    strokeLinecap="round"
                  />
                )}
              </g>
            )
          })}

          {/* Ghost Ring Template Preview */}
          {ringGhost && ringGhost.points?.length > 2 && (
            <g className="pointer-events-none">
              <polygon
                points={ringGhost.points.map((p) => `${p.x},${p.y}`).join(' ')}
                fill="none"
                stroke="#1d7f68"
                strokeWidth="1.8"
                strokeDasharray="5 3"
                opacity="0.65"
              />
              {ringGhost.points.map((p, idx) => (
                <circle key={idx} cx={p.x} cy={p.y} r="3" fill="#1d7f68" opacity="0.55" />
              ))}
            </g>
          )}

          {/* Hover Bond Sprout Preview */}
          {sproutPreview && (
            <g className="pointer-events-none" opacity="0.82">
              {activeTool === 'bond' && (
                <>
                  <line
                    x1={sproutPreview.x1}
                    y1={sproutPreview.y1}
                    x2={sproutPreview.x2}
                    y2={sproutPreview.y2}
                    stroke="#1d7f68"
                    strokeWidth="1.5"
                    strokeDasharray="3.5 2.5"
                  />
                  <circle cx={sproutPreview.x2} cy={sproutPreview.y2} r="3.5" fill="#1d7f68" />
                </>
              )}
              {activeElement && (activeTool === 'atom' || activeElement !== 'C') && (
                <text
                  x={activeTool === 'atom' ? sproutPreview.x1 : sproutPreview.x2}
                  y={(activeTool === 'atom' ? sproutPreview.y1 : sproutPreview.y2) - 15}
                  textAnchor="middle"
                  fontSize="11"
                  fontWeight="700"
                  fill="#1d7f68"
                >
                  {activeTool === 'atom' ? `→ ${activeElement}` : `+${activeElement}`}
                </text>
              )}
            </g>
          )}

          {/* Active Bond Drag Preview */}
          {dragState && (dragState.mode === 'draw_bond' || dragState.mode === 'new_bond') && (
            <g className="pointer-events-none">
              <line
                x1={dragState.fromX}
                y1={dragState.fromY}
                x2={dragState.toX}
                y2={dragState.toY}
                stroke="#1d7f68"
                strokeWidth={lineWidthPx}
                strokeDasharray="4 3"
              />
              <circle
                cx={dragState.toX}
                cy={dragState.toY}
                r={5.5}
                fill="rgba(29, 127, 104, 0.2)"
                stroke="#1d7f68"
                strokeWidth="1.5"
              />
            </g>
          )}

          {/* Active Chain Tool Drag Preview */}
          {dragState && dragState.mode === 'draw_chain' && dragState.points?.length > 1 && (
            <g className="pointer-events-none">
              <polyline
                points={dragState.points.map((p) => `${p.x},${p.y}`).join(' ')}
                fill="none"
                stroke="#1d7f68"
                strokeWidth={lineWidthPx}
                strokeDasharray="4 2.5"
              />
              {dragState.points.map((p, i) => (
                <circle key={i} cx={p.x} cy={p.y} r="3.5" fill="#1d7f68" />
              ))}
              <g
                transform={`translate(${dragState.points[dragState.points.length - 1].x + 14}, ${
                  dragState.points[dragState.points.length - 1].y - 14
                })`}
              >
                <rect x="-14" y="-9" width="28" height="18" rx="3" fill="#1d7f68" />
                <text
                  x="0"
                  y="0.5"
                  textAnchor="middle"
                  dominantBaseline="central"
                  fontSize="10"
                  fontWeight="700"
                  fill="#ffffff"
                >
                  C{dragState.points.length}
                </text>
              </g>
            </g>
          )}

          {/* Active Marquee Selection Box */}
          {dragState && dragState.mode === 'marquee' && (
            <rect
              x={Math.min(dragState.startX, dragState.curX)}
              y={Math.min(dragState.startY, dragState.curY)}
              width={Math.abs(dragState.curX - dragState.startX)}
              height={Math.abs(dragState.curY - dragState.startY)}
              fill="rgba(29, 127, 104, 0.12)"
              stroke="#1d7f68"
              strokeWidth="1.2"
              strokeDasharray="4 2"
            />
          )}

          {/* Active Lasso Selection Path */}
          {dragState && dragState.mode === 'lasso' && dragState.points.length > 1 && (
            <polygon
              points={dragState.points.map((p) => `${p.x},${p.y}`).join(' ')}
              fill="rgba(29, 127, 104, 0.12)"
              stroke="#1d7f68"
              strokeWidth="1.5"
              strokeDasharray="4 3"
            />
          )}

          {/* Render Atoms & ChemDraft Validation Badges */}
          {atoms.map((atom) => {
            const state = verification?.atomStateById?.get(atom.id)
            const degree = degreeById.get(atom.id) || 0
            const display = formatAtomDisplay(atom, state, degree, {
              showImplicitH,
              showCarbons,
            })
            const isHovered = hoveredAtomId === atom.id || highlightedAtomId === atom.id
            const isEraseHover = isHovered && activeTool === 'erase'
            const isInvalid = state && !state.valid
            const isWarn = state?.tautomerGuessed

            return (
              <g
                key={atom.id}
                className="cursor-pointer"
                onMouseEnter={() => setHoveredAtomId(atom.id)}
                onMouseLeave={() => setHoveredAtomId(null)}
                onPointerDown={(e) => handleAtomPointerDown(e, atom)}
                onDoubleClick={(e) => {
                  e.stopPropagation()
                  setEditingAtom({
                    id: atom.id,
                    x: atom.x,
                    y: atom.y,
                    value: atom.element || 'C',
                  })
                }}
              >
                <circle cx={atom.x} cy={atom.y} r={15} fill="transparent" />

                {highlightedAtomId === atom.id && (
                  <circle
                    cx={atom.x}
                    cy={atom.y}
                    r={16}
                    fill="rgba(245, 158, 11, 0.18)"
                    stroke="#f59e0b"
                    strokeWidth={2}
                  />
                )}

                {isHovered && (
                  <circle
                    cx={atom.x}
                    cy={atom.y}
                    r={10.5}
                    fill={isEraseHover ? '#fde8e7' : 'rgba(29, 127, 104, 0.16)'}
                    stroke={isEraseHover ? '#b3261e' : '#1d7f68'}
                    strokeWidth={1.4}
                  />
                )}

                {display ? (
                  <>
                    <circle
                      cx={atom.x}
                      cy={atom.y}
                      r={Math.max(10, display.baseText.length * 4.2)}
                      fill="#ffffff"
                      opacity={isHovered || selectedAtomIds.has(atom.id) ? 0.55 : 0.92}
                    />
                    <text
                      x={atom.x}
                      y={atom.y}
                      textAnchor="middle"
                      dominantBaseline="central"
                      fontSize={fontSizePx}
                      fontWeight="600"
                      fontFamily="Arial, Helvetica, sans-serif"
                      fill={isInvalid ? (isWarn ? '#b45309' : '#b3261e') : display.color}
                    >
                      {renderSubscriptedLabel(display.baseText)}
                      {(display.chargeText || display.radText) && (
                        <tspan dy="-6" fontSize={Math.max(10, fontSizePx * 0.72)} fontWeight="700">
                          {display.chargeText}
                          {display.radText}
                        </tspan>
                      )}
                    </text>
                  </>
                ) : (
                  <circle
                    cx={atom.x}
                    cy={atom.y}
                    r={isHovered ? 3.5 : Math.max(1.1, lineWidthPx * 0.55)}
                    fill={isHovered ? '#1d7f68' : '#1a211e'}
                  />
                )}

                {isInvalid && (
                  <g
                    className="native-atom-invalid-marker cursor-pointer"
                    transform={`translate(${atom.x + 11}, ${atom.y - 11})`}
                    onPointerDown={(e) => {
                      if (
                        state.expectedFormalCharge !== undefined &&
                        state.expectedFormalCharge !== state.formalCharge
                      ) {
                        e.stopPropagation()
                        onCommit(
                          atoms.map((a) =>
                            a.id === atom.id ? { ...a, formalCharge: state.expectedFormalCharge } : a
                          ),
                          bonds
                        )
                      }
                    }}
                  >
                    <title>
                      {state.invalidReason}
                      {state.expectedFormalCharge !== undefined
                        ? ` (Click ! to auto-fix formal charge to ${state.expectedFormalCharge > 0 ? `+${state.expectedFormalCharge}` : state.expectedFormalCharge})`
                        : ''}
                    </title>
                    <circle
                      r="6.5"
                      fill="#ffffff"
                      stroke={isWarn ? '#d97706' : '#b3261e'}
                      strokeWidth="1.6"
                    />
                    <text
                      x="0"
                      y="0.5"
                      textAnchor="middle"
                      dominantBaseline="central"
                      fontSize="9"
                      fontWeight="800"
                      fill={isWarn ? '#d97706' : '#b3261e'}
                    >
                      !
                    </text>
                  </g>
                )}
              </g>
            )
          })}
        </g>
      </svg>

      {/* Bottom-Left Live Lean 4 Vertex Inspector HUD */}
      {inspectedAtom && inspectedState && (
        <div className="absolute bottom-3 left-3 z-20 flex flex-wrap items-center gap-2 px-3 py-1.5 rounded-xl bg-slate-900/92 backdrop-blur-md text-white text-xs shadow-md border border-slate-700/80 max-w-[72%]">
          <span className="font-mono font-bold text-teal-300">
            {inspectedState.leanIdx !== undefined ? `Fin ${inspectedState.leanIdx}` : inspectedAtom.id}{' '}
            ({inspectedAtom.element})
          </span>
          <span className="text-slate-500">·</span>
          <span className="font-mono text-[11px] text-slate-200">
            valence: {inspectedState.valenceUsed}/{inspectedState.allowedValence}
          </span>
          <span className="text-slate-500">·</span>
          <span className="font-mono text-[11px] text-slate-200">
            H: {inspectedState.implicitH}
          </span>
          {inspectedState.symmetryRank !== undefined && (
            <>
              <span className="text-slate-500">·</span>
              <span className="font-mono text-[11px] text-sky-300">
                class {inspectedState.symmetryRank}
              </span>
            </>
          )}
          {inspectedAtom.formalCharge ? (
            <>
              <span className="text-slate-500">·</span>
              <span className="font-mono text-[11px] text-amber-300">
                charge: {inspectedAtom.formalCharge > 0 ? `+${inspectedAtom.formalCharge}` : inspectedAtom.formalCharge}
              </span>
            </>
          ) : null}
          {!inspectedState.valid && (
            <>
              <span className="text-slate-500">·</span>
              <span className="text-rose-300 font-medium truncate">{inspectedState.invalidReason}</span>
              {inspectedState.expectedFormalCharge !== undefined &&
                inspectedState.expectedFormalCharge !== inspectedState.formalCharge && (
                  <button
                    type="button"
                    onClick={() =>
                      onCommit(
                        atoms.map((a) =>
                          a.id === inspectedAtom.id
                            ? { ...a, formalCharge: inspectedState.expectedFormalCharge }
                            : a
                        ),
                        bonds
                      )
                    }
                    className="ml-1 px-2 py-0.5 rounded bg-amber-400 hover:bg-amber-300 text-slate-950 font-semibold text-[10px] inline-flex items-center gap-1 cursor-pointer shrink-0"
                  >
                    <Wand2 className="w-2.5 h-2.5" />
                    Fix Charge
                  </button>
                )}
            </>
          )}
        </div>
      )}

      {/* Bottom-Right Floating Zoom & Fit HUD */}
      <div className="absolute bottom-3 right-3 z-20 flex items-center gap-1 p-1 rounded-xl bg-white/92 backdrop-blur-md border border-slate-200/90 shadow-sm text-xs">
        <button
          type="button"
          onClick={() => setZoom((z) => Math.max(0.5, Math.round((z - 0.15) * 100) / 100))}
          title="Zoom Out"
          className="p-1.5 rounded-lg hover:bg-slate-100 text-slate-600 hover:text-slate-900 cursor-pointer"
        >
          <ZoomOut className="w-3.5 h-3.5" />
        </button>
        <button
          type="button"
          onClick={() => {
            setZoom(1)
            setPan({ x: 0, y: 0 })
          }}
          title="Reset Zoom to 100%"
          className="px-1.5 py-0.5 rounded-md hover:bg-slate-100 font-mono text-[11px] font-semibold text-slate-700 cursor-pointer"
        >
          {Math.round(zoom * 100)}%
        </button>
        <button
          type="button"
          onClick={() => setZoom((z) => Math.min(2.0, Math.round((z + 0.15) * 100) / 100))}
          title="Zoom In"
          className="p-1.5 rounded-lg hover:bg-slate-100 text-slate-600 hover:text-slate-900 cursor-pointer"
        >
          <ZoomIn className="w-3.5 h-3.5" />
        </button>
        <div className="w-px h-4 bg-slate-200 mx-0.5" />
        <button
          type="button"
          onClick={handleFitView}
          title="Center & Fit Molecule to Canvas (F)"
          className="px-2 py-1 rounded-lg hover:bg-teal-50 text-slate-700 hover:text-teal-800 font-medium text-[11px] inline-flex items-center gap-1 cursor-pointer"
        >
          <Maximize2 className="w-3 h-3" />
          Fit
        </button>
      </div>

      {/* Inline Atom / Functional Group Label Editor */}
      {editingAtom && svgRef.current && (() => {
        const rect = svgRef.current.getBoundingClientRect()
        const screenX = editingAtom.x * zoom + pan.x
        const screenY = editingAtom.y * zoom + pan.y
        const leftPx = (screenX / viewSize.w) * rect.width
        const topPx = (screenY / viewSize.h) * rect.height
        return (
          <div
            style={{ left: `${leftPx}px`, top: `${topPx}px` }}
            className="absolute -translate-x-1/2 -translate-y-1/2 z-30"
          >
            <input
              ref={labelInputRef}
              type="text"
              value={editingAtom.value}
              onChange={(e) => setEditingAtom({ ...editingAtom, value: e.target.value })}
              onKeyDown={(e) => {
                if (e.key === 'Enter') commitInlineLabel()
                if (e.key === 'Escape') setEditingAtom(null)
              }}
              onBlur={commitInlineLabel}
              placeholder="Atom / group (NH2, OH...)"
              className="w-28 px-2 py-0.5 text-xs font-mono font-semibold text-center bg-white border-2 border-[#1d7f68] rounded shadow-md focus:outline-none"
            />
          </div>
        )
      })()}
    </div>
  )
}
