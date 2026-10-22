/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
import LeanSMILES.Chem.Molecule

/-!
# LeanSMILES.SMILES.Write

From a `Molecule` back to a SMILES string, given a *rank* on the atoms that
says where to start and which neighbour to visit first.  Two passes, as in
every SMILES writer since Weininger (1989):

1. `dfs` walks a spanning forest, visiting neighbours in rank order, and
   records the bonds it meets that lead back to an already-visited atom — the
   ring closures.
2. `emit` writes the forest: the atom, its ring-closure digits (lowest free
   digit at the opening, freed at the closing), then every child but the last
   in parentheses.

With the identity rank, `toSmiles` writes the molecule in its stored atom
order; with `canonicalRanks` (`LeanSMILES.SMILES.Canon`) it writes the
canonical SMILES.  Everything the writer decides it decides from ranks and
bond kinds alone, so when the ranks are label-independent, so is the string.

Not written: the `/` `\` direction marks (recorded on bonds, but their meaning
depends on the walk, so writing them correctly needs the parity bookkeeping
that is out of scope here).  Chirality marks are written as recorded.
-/

namespace LeanSMILES.Molecule

variable {n : ℕ}

/-- The bond symbol the parser's implicit-kind rule makes redundant is
omitted: a single bond is written only between two aromatic atoms, an aromatic
bond only when not between two aromatic atoms. -/
def bondSymbol (a b : Atom) : BondKind → String
  | .single => if a.aromatic && b.aromatic then "-" else ""
  | .aromatic => if a.aromatic && b.aromatic then "" else ":"
  | k => k.symbol

/-- `1`–`9`, then `%10`, `%11`, … -/
def ringDigit (d : ℕ) : String := if d < 10 then toString d else s!"%{d}"

/-- Rank order, with the stored index to break ties. -/
def rankLE (rank : Fin n → ℕ) (i j : Fin n) : Bool :=
  decide (rank i < rank j ∨ (rank i = rank j ∧ i.val ≤ j.val))

/-- The bonds at `a`, by the rank of the atom at the other end. -/
def sortedBondsAt (m : Molecule n) (rank : Fin n → ℕ) (a : Fin n) : List (Bond n) :=
  (m.bondsAt a).mergeSort fun b c ↦ rankLE rank (b.other a) (c.other a)

/-! ### Pass 1: the spanning forest and the ring closures -/

/-- The state of the depth-first walk. -/
structure Walk (n : ℕ) where
  /-- Atoms visited so far. -/
  visited : Vector Bool n
  /-- Each atom's parent in the spanning forest. -/
  parent : Vector (Option (Fin n)) n
  /-- Tree children, in visit order. -/
  children : Vector (List (Fin n)) n
  /-- Bonds that close rings, each once. -/
  closures : List (Bond n)

/-- The walk before any atom is visited. -/
def Walk.init : Walk n :=
  ⟨Vector.replicate n false, Vector.replicate n none, Vector.replicate n [], []⟩

/-- Depth-first walk from `a`; `fuel` bounds the depth (`n + 1` suffices). -/
def dfs (m : Molecule n) (rank : Fin n → ℕ) : ℕ → Fin n → Walk n → Walk n
  | 0, _, w => w
  | fuel + 1, a, w₀ =>
    let w₀ := { w₀ with visited := w₀.visited.set a.val true a.isLt }
    (m.sortedBondsAt rank a).foldl (init := w₀) fun w b ↦
      let o := b.other a
      if w.parent[a] = some o then w
      else if w.visited[o] then
        if w.closures.any (·.edge == b.edge) then w else { w with closures := b :: w.closures }
      else
        let w := { w with
          parent := w.parent.set o.val (some a) o.isLt
          children := w.children.set a.val (w.children[a] ++ [o]) a.isLt }
        dfs m rank fuel o w

/-! ### Pass 2: the string -/

/-- The state of the writer. -/
structure Emit (n : ℕ) where
  /-- The string so far. -/
  out : String
  /-- Ring closures opened and not yet closed, with their digit. -/
  opened : List (Sym2 (Fin n) × ℕ)

/-- The smallest digit from `1` not in use. -/
def freeDigit (used : List ℕ) : ℕ := go (used.length + 1) 1
where
  /-- The first candidate from `d` not in use, with fuel. -/
  go : ℕ → ℕ → ℕ
    | 0, d => d
    | fuel + 1, d => if used.contains d then go fuel (d + 1) else d

/-- Write the ring-closure digits at `a`. -/
def emitClosures (m : Molecule n) (a : Fin n) (cls : List (Bond n)) (e : Emit n) : Emit n :=
  cls.foldl (init := e) fun e c ↦
    match e.opened.lookup c.edge with
    | some d => { out := e.out ++ ringDigit d, opened := e.opened.filter (·.1 != c.edge) }
    | none =>
      let d := freeDigit (e.opened.map (·.2))
      { out := e.out ++ bondSymbol (m.atom a) (m.atom (c.other a)) c.kind ++ ringDigit d,
        opened := (c.edge, d) :: e.opened }

/-- Write the subtree at `a`. -/
def emit (m : Molecule n) (rank : Fin n → ℕ) (w : Walk n) : ℕ → Fin n → Emit n → Emit n
  | 0, _, e => e
  | fuel + 1, a, e =>
    let e := { e with out := e.out ++ (m.atom a).toSmiles }
    let cls := (w.closures.filter (·.touches a)).mergeSort fun b c ↦
      rankLE rank (b.other a) (c.other a)
    let e := emitClosures m a cls e
    let kids := w.children[a]
    let numKids := kids.length
    kids.zipIdx.foldl (init := e) fun e ⟨o, k⟩ ↦
      let sym := match m.bondBetween a o with
        | some b => bondSymbol (m.atom a) (m.atom o) b.kind
        | none => ""
      if k + 1 < numKids then
        let e' := emit m rank w fuel o { e with out := e.out ++ "(" ++ sym }
        { e' with out := e'.out ++ ")" }
      else emit m rank w fuel o { e with out := e.out ++ sym }

/-- Write the molecule, starting each component at its lowest-ranked atom and
visiting neighbours in rank order; components are joined by `.` in order of
their start atom. -/
def write (m : Molecule n) (rank : Fin n → ℕ) : String :=
  let order := (List.finRange n).mergeSort (rankLE rank)
  let ⟨w, roots⟩ := order.foldl (init := ((Walk.init : Walk n), ([] : List (Fin n))))
    fun ⟨w, roots⟩ s ↦
      if w.visited[s] then (w, roots) else (dfs m rank (n + 1) s w, roots ++ [s])
  let e := roots.foldl (init := (⟨"", []⟩ : Emit n)) fun e r ↦
    let e := if e.out.isEmpty then e else { e with out := e.out ++ "." }
    emit m rank w (n + 1) r e
  e.out

/-- The molecule written in its stored atom order. -/
def toSmiles (m : Molecule n) : String := m.write (·.val)

end LeanSMILES.Molecule

namespace LeanSMILES

/-- A bundled molecule written in its stored atom order. -/
def Mol.toSmiles (M : Mol) : String := M.mol.toSmiles

end LeanSMILES
