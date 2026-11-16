import React, {
  useState,
  useEffect,
  useMemo,
  useRef,
  useCallback,
} from "react";
import { useNavigate } from "react-router-dom";
import {
  Undo2,
  Redo2,
  Copy,
  Check,
  Download,
  ExternalLink,
  Wand2,
  Sparkles,
  Trash2,
  ShieldCheck,
  AlertTriangle,
  Crosshair,
  Terminal,
} from "lucide-react";
import api, { newRequestHandle } from "../middleware/api";
import LeanCanvas, { ELEMENT_COLORS } from "../leandraw/LeanCanvas";
import {
  serializeDrawnGraph,
  graphToMolfileV2000,
  cleanupStructure2D,
} from "../leandraw/chemistryCore";
import { LEANDRAW_PRESETS } from "../leandraw/presets";
import { toolbarAsset } from "../leandraw/toolbarAssets";
import {
  Card,
  Badge,
  BusyBar,
  SpinnerPill,
  highlightLeanTokens,
} from "../components/UI";
import "../leandraw/leandraw.css";

// Narrow tall atom palette items (with covalent valences matching LeanSMILES.Valence)
const ATOM_PALETTE_ITEMS = [
  { symbol: "C", name: "Carbon", valence: 4 },
  { symbol: "N", name: "Nitrogen", valence: 3 },
  { symbol: "O", name: "Oxygen", valence: 2 },
  { symbol: "S", name: "Sulfur", valence: 2 },
  { symbol: "P", name: "Phosphorus", valence: 3 },
  { symbol: "F", name: "Fluorine", valence: 1 },
  { symbol: "Cl", name: "Chlorine", valence: 1 },
  { symbol: "Br", name: "Bromine", valence: 1 },
  { symbol: "I", name: "Iodine", valence: 1 },
  { symbol: "B", name: "Boron", valence: 3 },
  { symbol: "Si", name: "Silicon", valence: 4 },
  { symbol: "H", name: "Hydrogen", valence: 1 },
];

// Functional group superatoms (auto-expanded into full subgraphs in chemistryCore.js)
const GROUP_PALETTE_ITEMS = [
  { symbol: "OH", title: "Hydroxyl (-OH)" },
  { symbol: "NH2", title: "Primary Amine (-NH2)" },
  { symbol: "OMe", title: "Methoxy (-OCH3)" },
  { symbol: "NO2", title: "Nitro (-NO2)" },
  { symbol: "CF3", title: "Trifluoromethyl (-CF3)" },
  { symbol: "CO2H", title: "Carboxylic Acid (-COOH)" },
  { symbol: "CHO", title: "Aldehyde (-CHO)" },
  { symbol: "CN", title: "Nitrile / Cyano (-C≡N)" },
  { symbol: "Ph", title: "Phenyl Ring (-C6H5)" },
  { symbol: "SH", title: "Thiol (-SH)" },
  { symbol: "Boc", title: "tert-Butoxycarbonyl (-Boc)" },
  { symbol: "Ac", title: "Acetyl (-COCH3)" },
];

const RING_FLYOUT_ITEMS = [
  { id: "benzene", label: "Benzene", icon: "Custom_Benzene" },
  { id: "cyclohexane", label: "Cyclohexane", icon: "Custom_Cyclohexane" },
  { id: "cyclopentane", label: "Cyclopentane", icon: "Custom_Cyclopentane" },
  { id: "cyclopropane", label: "Cyclopropane", icon: "Custom_Cyclopentane" },
  { id: "cyclobutane", label: "Cyclobutane", icon: "Custom_Cyclopentane" },
  { id: "cycloheptane", label: "Cycloheptane", icon: "Custom_Cyclohexane" },
  { id: "cyclooctane", label: "Cyclooctane", icon: "Custom_Cyclohexane" },
  { id: "pyridine", label: "Pyridine", icon: "Custom_Benzene" },
  { id: "pyrrole", label: "Pyrrole", icon: "Custom_Cyclopentane" },
  { id: "chair1", label: "Chair", icon: "Custom_Chair1" },
];

export default function LeanDraw() {
  const navigate = useNavigate();
  const [selectedPresetId, setSelectedPresetId] = useState("");
  const [atoms, setAtoms] = useState([]);
  const [bonds, setBonds] = useState([]);
  const [history, setHistory] = useState([{ atoms: [], bonds: [] }]);
  const [historyIdx, setHistoryIdx] = useState(0);

  // Active drawing tool & chemistry state (default: Carbon atom & empty canvas)
  const [activeTool, setActiveTool] = useState("bond");
  const [activeBondOrder, setActiveBondOrder] = useState("single");
  const [activeBondStereo, setActiveBondStereo] = useState(null);
  const [activeBondStyle, setActiveBondStyle] = useState(null);
  const [activeRing, setActiveRing] = useState("benzene");
  const [activeElement, setActiveElement] = useState("C");
  const [selectedAtomIds, setSelectedAtomIds] = useState(() => new Set());
  const [highlightedAtomId, setHighlightedAtomId] = useState(null);

  const [openFlyout, setOpenFlyout] = useState(null);

  // LeanSMILES-focused canvas display settings
  const [styleSettings, setStyleSettings] = useState({
    strokeColor: "#20242a",
    lineWidthPx: 2,
    showImplicitH: true,
    showCarbons: false,
    fontFamily: "Arial",
    fontSizePx: 15,
    bondSpacingPct: 18,
    showCrosshairs: true,
  });

  // Bottom split section state
  const [codeTab, setCodeTab] = useState("lean"); // 'lean' | 'graph' | 'molfile'
  const [copiedSmiles, setCopiedSmiles] = useState(false);
  const [copiedCode, setCopiedCode] = useState(false);

  // Live Lean 4 verification state (all chemical verification runs in Lean 4 via Worker.lean)
  const [leanData, setLeanData] = useState(null);
  const [leanError, setLeanError] = useState(null);
  const [leanLoading, setLeanLoading] = useState(false);
  const [evalStartedAt, setEvalStartedAt] = useState(null);
  const leanReqId = useRef(0);
  const leanHandle = useRef(null);

  // Pure 2D graph-to-OpenSMILES serialization & Fin n vertex index mapping
  const serialized = useMemo(
    () => serializeDrawnGraph(atoms, bonds),
    [atoms, bonds],
  );

  // Build per-atom and whole-molecule verification state exclusively from Lean 4's response
  const verification = useMemo(() => {
    const leanAtoms = leanData?.atoms || [];
    const sanitizedAtoms = leanData?.aromatized?.ok
      ? leanData.aromatized.atoms || []
      : [];
    const aromFailed = leanData?.aromatized && leanData.aromatized.ok === false;
    const aromErrorMsg = aromFailed
      ? leanData.aromatized.message || "Can't kekulize mol"
      : null;

    const invalidValenceMap = new Map();
    if (Array.isArray(leanData?.valenceCheck?.invalidAtoms)) {
      leanData.valenceCheck.invalidAtoms.forEach((item) => {
        invalidValenceMap.set(item.atomIdx, item);
      });
    }

    const unresolvedAtomIds = new Set();
    const atomStates = atoms.map((atom) => {
      const leanIdx = serialized.leanIdxByDrawnAtomId.get(atom.id);
      const la = leanIdx !== undefined ? leanAtoms[leanIdx] : null;
      const sa = leanIdx !== undefined ? sanitizedAtoms[leanIdx] : null;
      const degree = serialized.degreeByDrawnId.get(atom.id) || 0;

      if (!la) {
        return {
          atomId: atom.id,
          leanIdx,
          element: atom.element,
          valenceUsed: degree,
          allowedValence: 4,
          implicitH: 0,
          formalCharge: atom.formalCharge || 0,
          valid: !leanError,
          ...(leanError ? { invalidReason: leanError } : {}),
        };
      }

      const chargeOk = la.chargeOk !== false;
      const valenceOk = la.valenceOk !== false;
      const valIssue = invalidValenceMap.get(leanIdx);
      const isAromAtom = Boolean(la.aromatic);
      const isAromError = Boolean(aromFailed && isAromAtom);
      if (isAromError) {
        unresolvedAtomIds.add(atom.id);
      }

      const valid = chargeOk && valenceOk && !isAromError;
      let invalidReason = null;
      if (!chargeOk) {
        invalidReason =
          leanData?.chargeCheck?.atomIdx === leanIdx
            ? leanData.chargeCheck.message
            : `atom ${leanIdx} (${la.symbol}) has invalid formal charge ${la.charge}`;
      } else if (!valenceOk) {
        invalidReason =
          valIssue?.message ||
          leanData?.valenceCheck?.message ||
          `atom ${leanIdx} (${la.symbol}) exceeds allowed valence (${la.explicitValence}/${la.allowedValence})`;
      } else if (isAromError) {
        invalidReason = `Mol.aromatize: ${aromErrorMsg}`;
      }

      const expectedFormalCharge =
        la.suggestedCharge !== null && la.suggestedCharge !== undefined
          ? la.suggestedCharge
          : sa && sa.charge !== la.charge
            ? sa.charge
            : undefined;

      return {
        atomId: atom.id,
        leanIdx,
        element: la.symbol || atom.element,
        valenceUsed: la.explicitValence ?? degree,
        allowedValence: la.allowedValence ?? 4,
        implicitH: sa?.totalH ?? la.totalH ?? 0,
        formalCharge: atom.formalCharge || 0,
        symmetryRank: la.symmetryRank,
        canonicalRank: la.canonicalRank,
        inRing: la.inRing,
        ...(expectedFormalCharge !== undefined ? { expectedFormalCharge } : {}),
        valid,
        ...(invalidReason ? { invalidReason } : {}),
      };
    });

    const atomStateById = new Map(atomStates.map((s) => [s.atomId, s]));
    const formula = leanData?.aromatized?.formula || leanData?.formula || "";

    return {
      smiles: serialized.smiles,
      canonicalSmiles:
        leanData?.aromatized?.canonicalSmiles ||
        leanData?.canonicalSmiles ||
        "",
      formula,
      expandedAtomCount: leanData?.n ?? serialized.expandedAtoms.length,
      expandedBondCount: leanData?.numBonds ?? serialized.expandedBonds.length,
      totalHydrogens:
        leanData?.aromatized?.totalHydrogens ?? leanData?.totalHydrogens ?? 0,
      symmetryClasses:
        leanData?.aromatized?.symmetryClasses ?? leanData?.symmetryClasses ?? 0,
      atomStates,
      atomStateById,
      unresolvedAtomIds,
      resolution: {
        unresolvedAtomIds,
        kekuleOrders: new Map(),
      },
      allValid:
        Boolean(leanData?.ok) &&
        !leanError &&
        leanData?.chargeCheck?.ok !== false &&
        leanData?.valenceCheck?.ok !== false &&
        leanData?.aromatized?.ok !== false,
    };
  }, [atoms, serialized, leanData, leanError]);

  const molfileV2000 = useMemo(
    () =>
      leanData?.aromatized?.molBlock ||
      leanData?.molBlock ||
      graphToMolfileV2000(atoms, bonds, verification.formula || "LeanSMILES"),
    [leanData, atoms, bonds, verification.formula],
  );

  // Close ring flyout when clicking outside
  useEffect(() => {
    if (!openFlyout) return;
    const close = () => setOpenFlyout(null);
    window.addEventListener("click", close);
    return () => window.removeEventListener("click", close);
  }, [openFlyout]);

  const commitGraph = useCallback(
    (nextAtoms, nextBonds, { recordHistory = true } = {}) => {
      setAtoms(nextAtoms);
      setBonds(nextBonds);
      if (recordHistory) {
        setHistory((prev) => {
          const sliced = prev.slice(0, historyIdx + 1);
          const updated = [
            ...sliced,
            { atoms: nextAtoms, bonds: nextBonds },
          ].slice(-40);
          setHistoryIdx(updated.length - 1);
          return updated;
        });
      }
    },
    [historyIdx],
  );

  const handleUndo = useCallback(() => {
    if (historyIdx <= 0) return;
    const prev = history[historyIdx - 1];
    setAtoms(prev.atoms);
    setBonds(prev.bonds);
    setHistoryIdx(historyIdx - 1);
  }, [history, historyIdx]);

  const handleRedo = useCallback(() => {
    if (historyIdx >= history.length - 1) return;
    const nxt = history[historyIdx + 1];
    setAtoms(nxt.atoms);
    setBonds(nxt.bonds);
    setHistoryIdx(historyIdx + 1);
  }, [history, historyIdx]);

  // Global tool & undo/redo keyboard shortcuts
  useEffect(() => {
    const onKeyDown = (e) => {
      const tag = document.activeElement?.tagName;
      if (tag === "INPUT" || tag === "TEXTAREA" || tag === "SELECT") return;

      if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === "z") {
        e.preventDefault();
        if (e.shiftKey) handleRedo();
        else handleUndo();
        return;
      }
      if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === "y") {
        e.preventDefault();
        handleRedo();
        return;
      }
      if (e.metaKey || e.ctrlKey || e.altKey) return;

      switch (e.key.toLowerCase()) {
        case "v":
          setActiveTool("select");
          break;
        case "l":
          setActiveTool("lasso");
          break;
        case "e":
          setActiveTool("erase");
          break;
        case "t":
          setActiveTool("text");
          break;
        case "1":
          setActiveTool("bond");
          setActiveBondOrder("single");
          setActiveBondStereo(null);
          setActiveBondStyle(null);
          break;
        case "2":
          setActiveTool("bond");
          setActiveBondOrder("double");
          setActiveBondStereo(null);
          setActiveBondStyle(null);
          break;
        case "3":
          setActiveTool("bond");
          setActiveBondOrder("triple");
          setActiveBondStereo(null);
          setActiveBondStyle(null);
          break;
        case "4":
          setActiveTool("bond");
          setActiveBondOrder("aromatic");
          setActiveBondStereo(null);
          setActiveBondStyle(null);
          break;
        case "r":
          setActiveTool("ring");
          setActiveRing("benzene");
          break;
        default:
          break;
      }
    };
    window.addEventListener("keydown", onKeyDown);
    return () => window.removeEventListener("keydown", onKeyDown);
  }, [handleUndo, handleRedo]);

  const loadPreset = (presetId) => {
    const preset = LEANDRAW_PRESETS.find((p) => p.id === presetId);
    if (!preset) return;
    setSelectedPresetId(presetId);
    commitGraph(preset.atoms, preset.bonds);
    setSelectedAtomIds(new Set(preset.atoms.map((a) => a.id)));
  };

  // Select an atom or superatom group from the narrow tall left palette box
  const handleSelectPaletteElement = (symbol) => {
    setActiveElement(symbol);
    if (activeTool !== "bond") {
      setActiveTool("atom");
    }
  };

  // Transform helpers (Flip Horizontal, Flip Vertical, Rotate 90°, Clean up 2D)
  const getTargetAtomSet = () =>
    selectedAtomIds.size > 0
      ? selectedAtomIds
      : new Set(atoms.map((a) => a.id));

  const getSelectionCenter = (targetAtoms) => {
    const xs = targetAtoms.map((a) => a.x);
    const ys = targetAtoms.map((a) => a.y);
    return {
      cx: (Math.min(...xs) + Math.max(...xs)) / 2,
      cy: (Math.min(...ys) + Math.max(...ys)) / 2,
    };
  };

  const handleFlip = (axis) => {
    const targetIds = getTargetAtomSet();
    const targetAtoms = atoms.filter((a) => targetIds.has(a.id));
    if (targetAtoms.length === 0) return;
    const { cx, cy } = getSelectionCenter(targetAtoms);
    const nextAtoms = atoms.map((a) => {
      if (!targetIds.has(a.id)) return a;
      return {
        ...a,
        x: axis === "h" ? Math.round((2 * cx - a.x) * 10) / 10 : a.x,
        y: axis === "v" ? Math.round((2 * cy - a.y) * 10) / 10 : a.y,
      };
    });
    commitGraph(nextAtoms, bonds);
  };

  const handleRotate90 = (degArg = 90) => {
    const deg = typeof degArg === "number" ? degArg : 90;
    const targetIds = getTargetAtomSet();
    const targetAtoms = atoms.filter((a) => targetIds.has(a.id));
    if (targetAtoms.length === 0) return;
    const { cx, cy } = getSelectionCenter(targetAtoms);
    const rad = (deg * Math.PI) / 180;
    const cos = Math.cos(rad);
    const sin = Math.sin(rad);
    const nextAtoms = atoms.map((a) => {
      if (!targetIds.has(a.id)) return a;
      const rx = a.x - cx;
      const ry = a.y - cy;
      return {
        ...a,
        x: Math.round((cx + rx * cos - ry * sin) * 10) / 10,
        y: Math.round((cy + rx * sin + ry * cos) * 10) / 10,
      };
    });
    commitGraph(nextAtoms, bonds);
  };

  const handleCleanup2D = () => {
    if (atoms.length < 2) return;
    const cleaned = cleanupStructure2D(atoms, bonds, selectedAtomIds);
    commitGraph(cleaned, bonds);
  };

  // Auto-fix formal charges suggested by Lean 4's `M.checkValence` / `M.aromatize`
  const fixableChargeStates = verification.atomStates.filter(
    (s) =>
      s.expectedFormalCharge !== undefined &&
      s.expectedFormalCharge !== s.formalCharge,
  );

  const handleAutoFixCharges = () => {
    if (!fixableChargeStates.length) return;
    const fixMap = new Map(
      fixableChargeStates.map((s) => [s.atomId, s.expectedFormalCharge]),
    );
    const nextAtoms = atoms.map((a) =>
      fixMap.has(a.id) ? { ...a, formalCharge: fixMap.get(a.id) } : a,
    );
    commitGraph(nextAtoms, bonds);
  };

  // Apply Lean 4's `M.aromatize` (Hückel 4n+2 perception & cleanUp) bond kinds onto drawn bonds
  const hasResolvedAromatic = useMemo(() => {
    if (
      !leanData?.aromatized?.ok ||
      !Array.isArray(leanData?.aromatized?.bonds)
    )
      return false;
    const aromBonds = leanData.aromatized.bonds;
    return bonds.some((b) => {
      const i1 = serialized.leanIdxByDrawnAtomId.get(b.fromAtomId);
      const i2 = serialized.leanIdxByDrawnAtomId.get(b.toAtomId);
      if (i1 === undefined || i2 === undefined) return false;
      const match = aromBonds.find(
        (ab) =>
          (ab.src === i1 && ab.dst === i2) || (ab.src === i2 && ab.dst === i1),
      );
      return match && match.kind !== (b.order || "single");
    });
  }, [leanData, bonds, serialized]);

  const handleKekulizeCanvas = () => {
    if (!leanData?.aromatized?.ok) return;
    const aromBonds = leanData.aromatized.bonds || [];
    const aromAtoms = leanData.aromatized.atoms || [];
    const nextAtoms = atoms.map((a) => {
      const idx = serialized.leanIdxByDrawnAtomId.get(a.id);
      const sa = idx !== undefined ? aromAtoms[idx] : null;
      return sa && sa.charge !== undefined
        ? { ...a, formalCharge: sa.charge }
        : a;
    });
    const nextBonds = bonds.map((b) => {
      const i1 = serialized.leanIdxByDrawnAtomId.get(b.fromAtomId);
      const i2 = serialized.leanIdxByDrawnAtomId.get(b.toAtomId);
      if (i1 === undefined || i2 === undefined) return b;
      const match = aromBonds.find(
        (ab) =>
          (ab.src === i1 && ab.dst === i2) || (ab.src === i2 && ab.dst === i1),
      );
      return match ? { ...b, order: match.kind } : b;
    });
    commitGraph(nextAtoms, nextBonds);
  };

  // Sync drawn SMILES with Lean 4 backend verifier
  useEffect(() => {
    const smi = serialized.smiles;
    const reqId = ++leanReqId.current;
    leanHandle.current?.cancel?.();
    if (!smi) {
      setLeanData(null);
      setLeanError(null);
      setLeanLoading(false);
      return;
    }
    const timer = setTimeout(async () => {
      const handle = newRequestHandle();
      leanHandle.current = handle;
      setLeanLoading(true);
      setEvalStartedAt(Date.now());
      setLeanError(null);
      try {
        const res = await api.analyzeSmiles(smi, handle);
        if (reqId !== leanReqId.current) return;
        setLeanData(res);
      } catch (err) {
        if (err?.cancelled || reqId !== leanReqId.current) return;
        setLeanData(null);
        setLeanError(
          err.details?.error || err.message || "Lean 4 verification failed",
        );
      } finally {
        if (reqId === leanReqId.current) {
          setLeanLoading(false);
          leanHandle.current = null;
        }
      }
    }, 220);
    return () => {
      clearTimeout(timer);
      leanHandle.current?.cancel?.();
    };
  }, [serialized.smiles]);

  const copySmiles = () => {
    const target = verification.canonicalSmiles || verification.smiles;
    if (!target) return;
    navigator.clipboard.writeText(target);
    setCopiedSmiles(true);
    setTimeout(() => setCopiedSmiles(false), 1800);
  };

  const downloadMolfile = () => {
    if (!atoms.length) return;
    const blob = new Blob([molfileV2000], {
      type: "chemical/x-mdl-molfile;charset=utf-8",
    });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `${verification.formula || "molecule"}.mol`;
    a.click();
    URL.revokeObjectURL(url);
  };

  const invalidStates = verification.atomStates.filter((s) => !s.valid);
  const leanChargeOk = leanData?.chargeCheck?.ok !== false;
  const leanValenceOk = leanData?.valenceCheck?.ok !== false;
  const leanAromOk = leanData?.aromatized?.ok !== false;

  const chargeCheckLabel = !leanData
    ? leanError
      ? "skipped"
      : "pending"
    : leanChargeOk
      ? "Except.ok ()"
      : `Except.error "${leanData.chargeCheck?.message}"`;

  const valenceCheckLabel = !leanData
    ? leanError
      ? "skipped"
      : "pending"
    : leanValenceOk
      ? "Except.ok ()"
      : `Except.error "${leanData.valenceCheck?.message}"`;

  const aromCheckLabel = !leanData
    ? leanError
      ? "skipped"
      : "pending"
    : leanAromOk
      ? `Except.ok "${leanData.aromatized?.canonicalSmiles || leanData.canonicalSmiles}"`
      : `Except.error "${leanData.aromatized?.message}"`;

  const overallVerified =
    Boolean(verification.smiles) &&
    Boolean(leanData?.ok) &&
    !leanError &&
    leanChargeOk &&
    leanValenceOk &&
    leanAromOk;

  // Compact Lean 4 verification script for the Left Bottom Split Panel
  const leanSpecCode = useMemo(() => {
    const smi = verification.smiles || "";
    if (!smi) {
      return [
        `open LeanSMILES LeanSMILES.SMILES`,
        ``,
        `def s : String := ""`,
      ].join("\n");
    }
    const nVertices = verification.expandedAtomCount;
    const morganPop = leanData?.morganBits?.length ?? 0;
    const parseOut = leanError
      ? `Except.error "${leanError}"`
      : `Except.ok (Molecule ${nVertices})`;

    return [
      `open LeanSMILES LeanSMILES.SMILES`,
      ``,
      `def s : String := "${smi}"`,
      `#eval parse s           --> ${parseOut}`,
      `#eval M.checkCharges    --> ${chargeCheckLabel}`,
      `#eval M.checkValence    --> ${valenceCheckLabel}`,
      `#eval M.aromatize       --> ${aromCheckLabel}`,
      `#eval M.morganBits.length --> ${morganPop}`,
    ].join("\n");
  }, [
    verification,
    leanData,
    leanError,
    chargeCheckLabel,
    valenceCheckLabel,
    aromCheckLabel,
  ]);

  // Compact SimpleGraph (Fin n) vertex & adjacency dump from Lean 4 for the 2nd Code Tab
  const leanGraphCode = useMemo(() => {
    const sourceAtoms = leanData?.atoms?.length
      ? leanData.atoms.map(
          (a) =>
            `${a.idx}:${a.symbol}${a.charge ? (a.charge > 0 ? `+${a.charge}` : a.charge) : ""}(H${a.totalH},c${a.symmetryRank})`,
        )
      : [];

    const sourceBonds = leanData?.bonds?.length
      ? leanData.bonds.map(
          (b) => `(${b.src},${b.dst}:${b.kind === "aromatic" ? "ar" : b.kind})`,
        )
      : [];

    return [
      `-- SimpleGraph (Fin ${leanData?.n ?? 0}) · ${leanData?.symmetryClasses ?? 0} symmetry classes`,
      `def atoms := #[${sourceAtoms.join(", ")}]`,
      `def bonds := #[${sourceBonds.join(", ")}]`,
      `def morganBits := [${(leanData?.morganBits || []).join(", ")}]`,
    ].join("\n");
  }, [leanData]);

  const displayedCode =
    codeTab === "lean"
      ? leanSpecCode
      : codeTab === "graph"
        ? leanGraphCode
        : molfileV2000;

  const handleCopyCode = () => {
    navigator.clipboard.writeText(displayedCode);
    setCopiedCode(true);
    setTimeout(() => setCopiedCode(false), 1800);
  };

  // Execution Logs for the Right Bottom Split Panel (from Worker.lean)
  const combinedLogs = useMemo(() => {
    if (!verification.smiles) {
      return [{ text: "Ready", kind: "info" }];
    }
    if (leanError) {
      return [
        {
          text: `SMILES.parse "${verification.smiles}" --> Except.error "${leanError}"`,
          kind: "err",
        },
      ];
    }
    if (!leanData?.logs?.length) {
      return [
        {
          text: `SMILES.parse "${verification.smiles}" --> Evaluating...`,
          kind: "info",
        },
      ];
    }

    return leanData.logs
      .filter((rawLine) => !rawLine.includes("Depict.svgWith"))
      .map((rawLine) => {
        const clean = rawLine
          .replace(/^>\s*/, "")
          .replace(/^#eval\s+/, "")
          .trim();
        const isErr =
          clean.includes("Except.error") ||
          clean.toLowerCase().includes("error");
        const atomMatch = clean.match(/atom\s+(\d+)/);
        const leanIdx = atomMatch ? Number(atomMatch[1]) : undefined;
        const atomId =
          leanIdx !== undefined
            ? serialized.drawnAtomIdByLeanIdx[leanIdx]
            : undefined;
        return {
          text: clean,
          kind: isErr ? "err" : clean.includes("-->") ? "ok" : "info",
          ...(atomId ? { atomId } : {}),
        };
      });
  }, [verification.smiles, leanError, leanData, serialized]);

  return (
    <div className="space-y-5">
      {/* Top Status & SMILES Bar */}
      <div className="glass rounded-2xl px-4 py-3 flex flex-wrap items-center justify-between gap-3">
        <div className="flex flex-wrap items-center gap-2.5 min-w-0 flex-1">
          {!verification.smiles ? (
            <Badge>Ready</Badge>
          ) : (
            <Badge
              tone={overallVerified ? "teal" : "amber"}
              active={overallVerified}
            >
              {overallVerified ? (
                <span className="inline-flex items-center gap-1.5 font-semibold">
                  <ShieldCheck className="w-3.5 h-3.5 text-teal-600" /> Verified
                </span>
              ) : leanLoading ? (
                <span className="inline-flex items-center gap-1.5 font-semibold">
                  Verifying...
                </span>
              ) : (
                <span className="inline-flex items-center gap-1.5 font-semibold">
                  <AlertTriangle className="w-3.5 h-3.5 text-amber-600" />{" "}
                  {invalidStates.length || 1}{" "}
                  {invalidStates.length === 1 ? "Issue" : "Issues"}
                </span>
              )}
            </Badge>
          )}

          {/* Canonical SMILES Pill */}
          <div className="flex items-center gap-2 bg-slate-900/[0.03] border border-slate-200/90 rounded-xl px-3 py-1.5 min-w-0 max-w-full sm:max-w-lg">
            <span className="text-[10px] font-bold uppercase tracking-wider text-slate-400 shrink-0">
              SMILES
            </span>
            <code
              className={`font-mono text-xs truncate ${
                verification.smiles ? "text-slate-800" : "text-slate-400"
              }`}
            >
              {verification.canonicalSmiles || verification.smiles || "Empty"}
            </code>
            <button
              type="button"
              onClick={copySmiles}
              disabled={!verification.smiles}
              title="Copy SMILES"
              className="p-1 rounded-md hover:bg-slate-200/70 text-slate-500 hover:text-slate-900 disabled:opacity-40 shrink-0 cursor-pointer"
            >
              {copiedSmiles ? (
                <Check className="w-3.5 h-3.5 text-emerald-600" />
              ) : (
                <Copy className="w-3.5 h-3.5" />
              )}
            </button>
          </div>

          {/* Lean 4 Formula & Graph Topology Pill */}
          {verification.smiles && (
            <div className="hidden xl:inline-flex items-center gap-2 px-2.5 py-1 rounded-lg bg-slate-100/80 border border-slate-200/60 text-xs text-slate-600 font-mono">
              {verification.formula && (
                <>
                  <span className="font-semibold text-slate-800">
                    {verification.formula}
                  </span>
                  <span className="text-slate-300">·</span>
                </>
              )}
              <span>
                Fin {verification.expandedAtomCount} (
                {verification.symmetryClasses} classes)
              </span>
            </div>
          )}
        </div>

        {/* Right: Open in Interpreter (/lab) */}
        <div className="flex flex-wrap items-center gap-2">
          <button
            type="button"
            disabled={!verification.smiles}
            onClick={() =>
              navigate(
                `/lab?smiles=${encodeURIComponent(leanData?.canonicalSmiles || verification.smiles)}`,
              )
            }
            className="h-8 px-3.5 rounded-xl bg-slate-900 hover:bg-slate-800 text-white text-xs font-medium inline-flex items-center gap-1.5 shadow-xs disabled:opacity-40 cursor-pointer transition"
          >
            <span>Open in Interpreter</span>
            <ExternalLink className="w-3.5 h-3.5" />
          </button>
        </div>
      </div>

      {/* Main 2D Molecular Studio Shell */}
      <div className="ld-workspace-shell ld-studio-frame">
        {/* Studio Header Bar */}
        <div className="ld-palette-title">
          <div className="flex items-center gap-2 min-w-0">
            <span className="w-2 h-2 rounded-full bg-teal-500 shrink-0" />
            <span className="truncate font-semibold text-slate-800">
              Structure Editor
            </span>
          </div>

          {/* Right-side Preset Selector & History Controls */}
          <div className="flex items-center gap-2">
            <select
              value={selectedPresetId}
              onChange={(e) => {
                if (e.target.value) loadPreset(e.target.value);
              }}
              className="h-6 px-2 text-[11px] font-medium rounded-lg border border-slate-300 bg-white text-slate-800 focus:outline-none focus:border-teal-600 cursor-pointer"
              title="Load preset"
            >
              <option value="">Presets...</option>
              <optgroup label="Molecules">
                {LEANDRAW_PRESETS.filter((p) => p.category === "valid").map(
                  (p) => (
                    <option key={p.id} value={p.id}>
                      {p.label}
                    </option>
                  ),
                )}
              </optgroup>
              <optgroup label="Verification Tests">
                {LEANDRAW_PRESETS.filter((p) => p.category === "verify").map(
                  (p) => (
                    <option key={p.id} value={p.id}>
                      {p.label}
                    </option>
                  ),
                )}
              </optgroup>
            </select>

            <div className="flex items-center gap-0.5 bg-white border border-slate-200/90 rounded-lg p-0.5">
              <button
                type="button"
                onClick={handleUndo}
                disabled={historyIdx <= 0}
                title="Undo"
                className="p-1 rounded hover:bg-slate-100 disabled:opacity-35 cursor-pointer"
              >
                <Undo2 className="w-3.5 h-3.5 text-slate-600" />
              </button>
              <button
                type="button"
                onClick={handleRedo}
                disabled={historyIdx >= history.length - 1}
                title="Redo"
                className="p-1 rounded hover:bg-slate-100 disabled:opacity-35 cursor-pointer"
              >
                <Redo2 className="w-3.5 h-3.5 text-slate-600" />
              </button>
              <button
                type="button"
                onClick={() => {
                  setSelectedPresetId("");
                  setSelectedAtomIds(new Set());
                  commitGraph([], []);
                }}
                title="Clear"
                className="p-1 rounded hover:bg-rose-50 text-slate-600 hover:text-rose-600 cursor-pointer"
              >
                <Trash2 className="w-3.5 h-3.5" />
              </button>
            </div>
          </div>
        </div>

        {/* Labeled Chemistry Tool Ribbon */}
        <div className="ld-tool-palette-scroll">
          <div className="ld-tool-palette">
            {/* SECTION 1: Select & Edit */}
            <div className="ld-tool-section">
              <div className="ld-tool-section-header">Select & Edit</div>
              <div className="ld-tool-group">
                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Select (V)"
                    onClick={() => setActiveTool("select")}
                    className={`ld-icon-button ${activeTool === "select" ? "active" : ""}`}
                  >
                    <img
                      src={toolbarAsset("Art_Select")}
                      alt="Select"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>
                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Lasso (L)"
                    onClick={() => setActiveTool("lasso")}
                    className={`ld-icon-button ${activeTool === "lasso" ? "active" : ""}`}
                  >
                    <img
                      src={toolbarAsset("Custom_Lasso")}
                      alt="Lasso"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>
                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Erase (E)"
                    onClick={() => setActiveTool("erase")}
                    className={`ld-icon-button ${activeTool === "erase" ? "active" : ""}`}
                  >
                    <img
                      src={toolbarAsset("Art_Eraser")}
                      alt="Eraser"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>
                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Label (T)"
                    onClick={() => setActiveTool("text")}
                    className={`ld-icon-button ${activeTool === "text" ? "active" : ""}`}
                  >
                    <img
                      src={toolbarAsset("Art_Text")}
                      alt="Label"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>
              </div>
            </div>

            {/* SECTION 2: Covalent Bonds & Stereochemistry */}
            <div className="ld-tool-section">
              <div className="ld-tool-section-header">Bonds & Stereo</div>
              <div className="ld-tool-group">
                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Single Bond (1)"
                    onClick={() => {
                      setActiveTool("bond");
                      setActiveBondOrder("single");
                      setActiveBondStereo(null);
                      setActiveBondStyle(null);
                    }}
                    className={`ld-icon-button ${
                      activeTool === "bond" &&
                      activeBondOrder === "single" &&
                      !activeBondStereo &&
                      !activeBondStyle
                        ? "active"
                        : ""
                    }`}
                  >
                    <img
                      src={toolbarAsset("Custom_Bond")}
                      alt="Single Bond"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Double Bond (2)"
                    onClick={() => {
                      setActiveTool("bond");
                      setActiveBondOrder("double");
                      setActiveBondStereo(null);
                      setActiveBondStyle(null);
                    }}
                    className={`ld-toolbar-text-button ${
                      activeTool === "bond" && activeBondOrder === "double"
                        ? "active"
                        : ""
                    }`}
                  >
                    =
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Triple Bond (3)"
                    onClick={() => {
                      setActiveTool("bond");
                      setActiveBondOrder("triple");
                      setActiveBondStereo(null);
                      setActiveBondStyle(null);
                    }}
                    className={`ld-toolbar-text-button ${
                      activeTool === "bond" && activeBondOrder === "triple"
                        ? "active"
                        : ""
                    }`}
                  >
                    ≡
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Aromatic Bond (4)"
                    onClick={() => {
                      setActiveTool("bond");
                      setActiveBondOrder("aromatic");
                      setActiveBondStereo(null);
                      setActiveBondStyle(null);
                    }}
                    className={`ld-toolbar-text-button text-[10px] ${
                      activeTool === "bond" && activeBondOrder === "aromatic"
                        ? "active"
                        : ""
                    }`}
                  >
                    Ar
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Wedge Bond"
                    onClick={() => {
                      setActiveTool("bond");
                      setActiveBondOrder("single");
                      setActiveBondStereo("up");
                      setActiveBondStyle(null);
                    }}
                    className={`ld-icon-button ${
                      activeTool === "bond" && activeBondStereo === "up"
                        ? "active"
                        : ""
                    }`}
                  >
                    <img
                      src={toolbarAsset("Custom_Bond_Wedge")}
                      alt="Wedge"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Hashed Bond"
                    onClick={() => {
                      setActiveTool("bond");
                      setActiveBondOrder("single");
                      setActiveBondStereo("down");
                      setActiveBondStyle(null);
                    }}
                    className={`ld-icon-button ${
                      activeTool === "bond" && activeBondStereo === "down"
                        ? "active"
                        : ""
                    }`}
                  >
                    <img
                      src={toolbarAsset("Custom_Bond_Hashed")}
                      alt="Hashed"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Carbon Chain"
                    onClick={() => setActiveTool("chain")}
                    className={`ld-icon-button ${activeTool === "chain" ? "active" : ""}`}
                  >
                    <img
                      src={toolbarAsset("Custom_Draw_Line")}
                      alt="Chain"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Dashed Bond"
                    onClick={() => {
                      setActiveTool("bond");
                      setActiveBondOrder("single");
                      setActiveBondStereo(null);
                      setActiveBondStyle("dashed");
                    }}
                    className={`ld-icon-button ${
                      activeTool === "bond" && activeBondStyle === "dashed"
                        ? "active"
                        : ""
                    }`}
                  >
                    <img
                      src={toolbarAsset("Custom_Bond_Dashed")}
                      alt="Dashed"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>
              </div>
            </div>

            {/* SECTION 3: Rings & Heterocycles */}
            <div className="ld-tool-section">
              <div className="ld-tool-section-header">Rings (R)</div>
              <div className="ld-tool-group">
                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Benzene (R)"
                    onClick={() => {
                      setActiveTool("ring");
                      setActiveRing("benzene");
                    }}
                    className={`ld-icon-button ${
                      activeTool === "ring" && activeRing === "benzene"
                        ? "active"
                        : ""
                    }`}
                  >
                    <img
                      src={toolbarAsset("Custom_Benzene")}
                      alt="Benzene"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Cyclohexane"
                    onClick={() => {
                      setActiveTool("ring");
                      setActiveRing("cyclohexane");
                    }}
                    className={`ld-icon-button ${
                      activeTool === "ring" && activeRing === "cyclohexane"
                        ? "active"
                        : ""
                    }`}
                  >
                    <img
                      src={toolbarAsset("Custom_Cyclohexane")}
                      alt="Cyclohexane"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Cyclopentane"
                    onClick={() => {
                      setActiveTool("ring");
                      setActiveRing("cyclopentane");
                    }}
                    className={`ld-icon-button ${
                      activeTool === "ring" && activeRing === "cyclopentane"
                        ? "active"
                        : ""
                    }`}
                  >
                    <img
                      src={toolbarAsset("Custom_Cyclopentane")}
                      alt="Cyclopentane"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="More Rings"
                    onClick={(e) => {
                      e.stopPropagation();
                      setOpenFlyout(openFlyout === "ring" ? null : "ring");
                    }}
                    className={`ld-icon-button ${
                      activeTool === "ring" &&
                      !["benzene", "cyclohexane", "cyclopentane"].includes(
                        activeRing,
                      )
                        ? "active"
                        : ""
                    }`}
                  >
                    <img
                      src={toolbarAsset("Custom_Chair1")}
                      alt="More Rings"
                      className="ld-tool-icon-image"
                    />
                    <span className="ld-flyout-indicator" />
                  </button>
                  {openFlyout === "ring" && (
                    <div
                      className="ld-flyout-menu"
                      onClick={(e) => e.stopPropagation()}
                    >
                      {RING_FLYOUT_ITEMS.map((item) => (
                        <button
                          key={item.id}
                          type="button"
                          onClick={() => {
                            setActiveTool("ring");
                            setActiveRing(item.id);
                            setOpenFlyout(null);
                          }}
                          className={`ld-flyout-item ${
                            activeTool === "ring" && activeRing === item.id
                              ? "active"
                              : ""
                          }`}
                        >
                          <img src={toolbarAsset(item.icon)} alt="" />
                          <span>{item.label}</span>
                        </button>
                      ))}
                    </div>
                  )}
                </div>
              </div>
            </div>

            {/* SECTION 4: Formal Charges & Radicals */}
            <div className="ld-tool-section">
              <div className="ld-tool-section-header">Valence & Charge</div>
              <div className="ld-tool-group">
                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Positive Charge (+)"
                    onClick={() => setActiveTool("charge_plus")}
                    className={`ld-icon-button ${activeTool === "charge_plus" ? "active" : ""}`}
                  >
                    <img
                      src={toolbarAsset("Custom_CirclePlus")}
                      alt="Charge +"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Negative Charge (-)"
                    onClick={() => setActiveTool("charge_minus")}
                    className={`ld-icon-button ${activeTool === "charge_minus" ? "active" : ""}`}
                  >
                    <img
                      src={toolbarAsset("Custom_CircleMinus")}
                      alt="Charge -"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Radical"
                    onClick={() => setActiveTool("radical")}
                    className={`ld-icon-button ${activeTool === "radical" ? "active" : ""}`}
                  >
                    <img
                      src={toolbarAsset("Custom_RadicalDot")}
                      alt="Radical"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Lone Pair"
                    onClick={() => setActiveTool("lone_pair")}
                    className={`ld-icon-button ${activeTool === "lone_pair" ? "active" : ""}`}
                  >
                    <img
                      src={toolbarAsset("Custom_LonePair")}
                      alt="Lone Pair"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>
              </div>
            </div>

            {/* SECTION 5: 2D Geometry & Transforms */}
            <div className="ld-tool-section">
              <div className="ld-tool-section-header">2D Geometry</div>
              <div className="ld-tool-group">
                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Clean Up 2D"
                    onClick={handleCleanup2D}
                    className="ld-icon-button"
                  >
                    <img
                      src={toolbarAsset("Custom_Structure_Cleanup")}
                      alt="Cleanup 2D"
                      className="ld-tool-icon-image cleanup-2d"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Rotate 90°"
                    onClick={handleRotate90}
                    className="ld-icon-button"
                  >
                    <img
                      src={toolbarAsset("Custom_Rotation")}
                      alt="Rotate 90°"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Flip Horizontal"
                    onClick={() => handleFlip("h")}
                    className="ld-icon-button"
                  >
                    <img
                      src={toolbarAsset("Custom_Flip_Horizontal")}
                      alt="Flip H"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>

                <div className="ld-icon-button-shell">
                  <button
                    type="button"
                    title="Flip Vertical"
                    onClick={() => handleFlip("v")}
                    className="ld-icon-button"
                  >
                    <img
                      src={toolbarAsset("Custom_Flip_Vertical")}
                      alt="Flip V"
                      className="ld-tool-icon-image"
                    />
                  </button>
                </div>
              </div>
            </div>

            {/* SECTION 6: Display & Actions */}
            <div className="ld-tool-section">
              <div className="ld-tool-section-header">Display & Actions</div>
              <div className="flex items-center gap-1.5">
                <button
                  type="button"
                  title="Implicit Hydrogens"
                  onClick={() =>
                    setStyleSettings((s) => ({
                      ...s,
                      showImplicitH: !s.showImplicitH,
                    }))
                  }
                  className={`ld-toolbar-text-button ${styleSettings.showImplicitH ? "active" : ""}`}
                >
                  H
                </button>
                <button
                  type="button"
                  title="Show Carbons"
                  onClick={() =>
                    setStyleSettings((s) => ({
                      ...s,
                      showCarbons: !s.showCarbons,
                    }))
                  }
                  className={`ld-toolbar-text-button ${styleSettings.showCarbons ? "active" : ""}`}
                >
                  C
                </button>
                <button
                  type="button"
                  title="Crosshairs"
                  onClick={() =>
                    setStyleSettings((s) => ({
                      ...s,
                      showCrosshairs: !s.showCrosshairs,
                    }))
                  }
                  className={`ld-toolbar-text-button ${styleSettings.showCrosshairs ? "active" : ""}`}
                >
                  <Crosshair className="w-3.5 h-3.5" />
                </button>

                {fixableChargeStates.length > 0 && (
                  <button
                    type="button"
                    onClick={handleAutoFixCharges}
                    className="h-[27px] px-2.5 rounded-md bg-amber-100 hover:bg-amber-200 border border-amber-400 text-amber-900 text-[11px] font-semibold inline-flex items-center gap-1 cursor-pointer transition"
                    title="Fix Formal Charges"
                  >
                    <Wand2 className="w-3 h-3" />
                    Fix Charge ({fixableChargeStates.length})
                  </button>
                )}

                {hasResolvedAromatic && (
                  <button
                    type="button"
                    onClick={handleKekulizeCanvas}
                    className="h-[27px] px-2.5 rounded-md bg-teal-50 hover:bg-teal-100 border border-teal-400 text-teal-900 text-[11px] font-semibold inline-flex items-center gap-1 cursor-pointer transition"
                    title="Kekulize"
                  >
                    <Sparkles className="w-3 h-3" />
                    Kekulize
                  </button>
                )}
              </div>
            </div>
          </div>
        </div>

        {/* Workspace Row: Narrow Tall Atom/Group Box (Left) + Full-Screen 2D Canvas (Right) */}
        <div className="flex items-stretch overflow-hidden rounded-b-[15px] bg-white">
          {/* Narrow Tall Atom & Functional Group Palette Box */}
          <aside
            className="ld-atom-sidebar h-[calc(100vh-275px)] min-h-[500px] max-h-[700px]"
            aria-label="Atom and Functional Group Palette"
          >
            {/* Elements Section */}
            <div className="ld-atom-sidebar-section">
              <div className="ld-atom-sidebar-title">
                <span>Atoms</span>
                <span className="font-mono text-[9.5px] text-teal-700 font-bold">
                  {activeElement}
                </span>
              </div>
              <div className="ld-atom-grid">
                {ATOM_PALETTE_ITEMS.map((item) => {
                  const isSelected = activeElement === item.symbol;
                  const color = ELEMENT_COLORS[item.symbol] || "#1e293b";
                  return (
                    <button
                      key={item.symbol}
                      type="button"
                      title={`${item.name} (${item.symbol})`}
                      onClick={() => handleSelectPaletteElement(item.symbol)}
                      className={`ld-atom-pill ${isSelected ? "active" : ""}`}
                    >
                      <span style={{ color }}>{item.symbol}</span>
                      <span className="ld-atom-valence">v{item.valence}</span>
                    </button>
                  );
                })}
              </div>
            </div>

            {/* Functional Group Superatoms Section */}
            <div className="ld-atom-sidebar-section border-b-0 flex-1">
              <div className="ld-atom-sidebar-title">
                <span>Groups</span>
              </div>
              <div className="ld-atom-grid">
                {GROUP_PALETTE_ITEMS.map((grp) => {
                  const isSelected = activeElement === grp.symbol;
                  return (
                    <button
                      key={grp.symbol}
                      type="button"
                      title={grp.title}
                      onClick={() => handleSelectPaletteElement(grp.symbol)}
                      className={`ld-group-pill ${isSelected ? "active" : ""}`}
                    >
                      -{grp.symbol}
                    </button>
                  );
                })}
              </div>
            </div>
          </aside>

          {/* 2D Chemical Canvas */}
          <LeanCanvas
            atoms={atoms}
            bonds={bonds}
            verification={verification}
            activeTool={activeTool}
            activeBondOrder={activeBondOrder}
            activeBondStereo={activeBondStereo}
            activeBondStyle={activeBondStyle}
            activeRing={activeRing}
            activeElement={activeElement}
            selectedAtomIds={selectedAtomIds}
            onSelectAtomIds={setSelectedAtomIds}
            styleSettings={styleSettings}
            onCommit={(nextAtoms, nextBonds, opts) =>
              commitGraph(nextAtoms, nextBonds, opts)
            }
            highlightedAtomId={highlightedAtomId}
          />
        </div>
      </div>

      {/* Live Lean 4 Evaluation Progress Bar (when active) */}
      {leanLoading && (
        <div className="flex justify-end">
          <BusyBar
            label="Evaluating in Lean 4..."
            startedAt={evalStartedAt}
            expectedMs={450}
            onCancel={() => {
              leanReqId.current += 1;
              leanHandle.current?.cancel?.();
              setLeanLoading(false);
            }}
          />
        </div>
      )}

      {/* Bottom Split Section: Left = Compact Lean 4 Code | Right = Compact Execution Logs */}
      <div className="grid grid-cols-1 lg:grid-cols-2 gap-4 items-stretch">
        {/* LEFT SPLIT: Compact Lean 4 Code / SimpleGraph / Molfile */}
        <Card
          className="!p-4"
          title="Lean 4 Code"
          action={
            <div className="flex items-center gap-1.5">
              <div className="inline-flex rounded-lg bg-slate-100 p-0.5 border border-slate-200/80">
                {[
                  { id: "lean", label: "Spec" },
                  { id: "graph", label: "Graph" },
                  { id: "molfile", label: ".mol" },
                ].map((t) => (
                  <button
                    key={t.id}
                    type="button"
                    onClick={() => setCodeTab(t.id)}
                    className={`px-2 py-0.5 rounded-md text-[11px] font-semibold transition cursor-pointer ${
                      codeTab === t.id
                        ? "bg-white text-slate-900 shadow-2xs"
                        : "text-slate-600 hover:text-slate-900"
                    }`}
                  >
                    {t.label}
                  </button>
                ))}
              </div>

              <button
                type="button"
                onClick={handleCopyCode}
                title="Copy Code"
                className="h-6 px-2 rounded-md border border-slate-200 bg-white hover:bg-slate-50 text-slate-600 hover:text-slate-900 text-[11px] font-medium inline-flex items-center gap-1 cursor-pointer"
              >
                {copiedCode ? (
                  <Check className="w-3 h-3 text-emerald-600" />
                ) : (
                  <Copy className="w-3 h-3" />
                )}
              </button>

              {codeTab === "molfile" && (
                <button
                  type="button"
                  onClick={downloadMolfile}
                  title="Download V2000 .mol file"
                  className="h-6 px-2 rounded-md border border-slate-200 bg-white hover:bg-slate-50 text-slate-600 hover:text-slate-900 text-[11px] font-medium inline-flex items-center gap-1 cursor-pointer"
                >
                  <Download className="w-3 h-3" />
                </button>
              )}
            </div>
          }
        >
          <div className="h-44 overflow-y-auto rounded-xl bg-[#0d131a] border border-slate-800/90 p-3 font-mono text-[11px] leading-relaxed text-[#c8d3f5] shadow-inner">
            <pre className="whitespace-pre-wrap break-words">
              {codeTab === "molfile"
                ? displayedCode
                : highlightLeanTokens(displayedCode)}
            </pre>
          </div>
        </Card>

        {/* RIGHT SPLIT: Compact Execution Logs */}
        <Card
          className="!p-4"
          title="Execution Logs"
          action={
            <div className="flex items-center gap-1.5">
              <span className="font-mono text-[11px] text-slate-500 mr-1">
                Fin {leanData?.n ?? verification.expandedAtomCount} ·{" "}
                {leanData?.numBonds ?? verification.expandedBondCount}b ·{" "}
                {leanData?.morganBits?.length ?? 0} bits
              </span>
              {leanLoading ? (
                <SpinnerPill label="Running" />
              ) : leanData?.leanFeedback ? (
                <Badge active>
                  {leanData.leanFeedback.durationMs}ms ·{" "}
                  {leanData.leanFeedback.cached ? "cached" : "live"}
                </Badge>
              ) : null}
            </div>
          }
        >
          {(invalidStates.length > 0 || leanError) && (
            <div className="mb-2 rounded-lg bg-amber-50/90 border border-amber-200/90 px-2.5 py-1 flex items-center justify-between gap-2 text-[11px]">
              {invalidStates.length > 0 ? (
                <span
                  onMouseEnter={() =>
                    setHighlightedAtomId(invalidStates[0].atomId)
                  }
                  onMouseLeave={() => setHighlightedAtomId(null)}
                  className="font-mono text-amber-900 truncate cursor-pointer"
                >
                  <strong>
                    Fin {invalidStates[0].leanIdx ?? invalidStates[0].atomId} (
                    {invalidStates[0].element})
                  </strong>
                  : {invalidStates[0].invalidReason}
                </span>
              ) : (
                <span className="font-mono text-amber-900 truncate">
                  <strong>Lean 4 ParseError</strong>: {leanError}
                </span>
              )}
              {fixableChargeStates.length > 0 && (
                <button
                  type="button"
                  onClick={handleAutoFixCharges}
                  className="px-2 py-0.5 rounded bg-amber-600 hover:bg-amber-700 text-white text-[10px] font-semibold inline-flex items-center gap-1 cursor-pointer shrink-0"
                >
                  <Wand2 className="w-2.5 h-2.5" /> Fix
                </button>
              )}
            </div>
          )}

          <div className="h-44 overflow-y-auto rounded-xl bg-[#0d131a] border border-slate-800/90 py-1.5 font-mono text-[11px] shadow-inner divide-y divide-slate-800/35">
            {combinedLogs.map((line, i) => {
              const parts = line.text.split("-->");
              return (
                <div
                  key={i}
                  onMouseEnter={() =>
                    line.atomId && setHighlightedAtomId(line.atomId)
                  }
                  onMouseLeave={() => line.atomId && setHighlightedAtomId(null)}
                  className="px-3 py-1 flex items-baseline justify-between gap-3 hover:bg-white/[0.03]"
                >
                  <span className="text-[#c8d3f5] truncate">
                    <span className="text-slate-600 select-none text-[10px] mr-2">
                      {String(i + 1).padStart(2, "0")}
                    </span>
                    {highlightLeanTokens(parts[0].trim())}
                  </span>
                  {parts.length === 2 && (
                    <span
                      className={`shrink-0 truncate max-w-[55%] font-medium ${
                        line.kind === "err"
                          ? "text-rose-400"
                          : line.kind === "warn"
                            ? "text-amber-300"
                            : "text-[#2ac3de]"
                      }`}
                    >
                      {parts[1].trim()}
                    </span>
                  )}
                </div>
              );
            })}
          </div>
        </Card>
      </div>
    </div>
  );
}
