import React from "react";
import { Routes, Route } from "react-router-dom";
import Home from "../pages/Home";
import Lab from "../pages/Lab";
import Datasets from "../pages/Datasets";
import LeanDraw from "../pages/LeanDraw";
import NotFound from "../pages/NotFound";

export default function AppRoutes() {
  return (
    <Routes>
      <Route path="/" element={<Home />} />
      <Route path="/lab" element={<Lab />} />
      <Route path="/draw" element={<LeanDraw />} />
      <Route path="/leandraw" element={<LeanDraw />} />
      <Route path="/datasets" element={<Datasets />} />
      <Route path="*" element={<NotFound />} />
    </Routes>
  );
}
