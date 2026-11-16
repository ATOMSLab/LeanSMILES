import React from "react";
import { useLocation } from "react-router-dom";
import Navbar from "./components/Navbar";
import AppRoutes from "./routes/AppRoutes";
import api from "./middleware/api";

export default function App() {
  const { pathname } = useLocation();
  const isWidePage = pathname === "/draw" || pathname === "/leandraw";

  return (
    <div
      className="min-h-screen flex flex-col overflow-x-hidden"
      data-api-ready={Boolean(api)}
    >
      <Navbar />
      <main
        className={`flex-1 w-full mx-auto px-4 sm:px-6 min-w-0 ${
          isWidePage ? "max-w-[1420px] py-5 sm:py-7" : "max-w-5xl py-6 sm:py-10"
        }`}
      >
        <AppRoutes />
      </main>
      <footer className="py-6 text-center text-xs text-slate-400">
        LeanSMILES ·{" "}
        <a
          href="https://atomslab.github.io"
          target="_blank"
          rel="noreferrer"
          className="hover:text-teal-700 hover:underline"
        >
          ATOMS Lab
        </a>{" "}
        ·{" "}
        <a
          href="https://github.com/ATOMSLab/LeanSMILES"
          target="_blank"
          rel="noreferrer"
          className="hover:text-teal-700 hover:underline"
        >
          Source on GitHub
        </a>
      </footer>
    </div>
  );
}
