import React from 'react'
import { Routes, Route } from 'react-router-dom'
import Home from '../pages/Home'
import Lab from '../pages/Lab'
import Datasets from '../pages/Datasets'
import ChemDraw from '../pages/ChemDraw'
import NotFound from '../pages/NotFound'

export default function AppRoutes() {
  return (
    <Routes>
      <Route path="/" element={<Home />} />
      <Route path="/lab" element={<Lab />} />
      <Route path="/chemdraw" element={<ChemDraw />} />
      <Route path="/datasets" element={<Datasets />} />
      <Route path="*" element={<NotFound />} />
    </Routes>
  )
}
