/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Chem.Molecule

/-!
# LeanSMILES.SMILES.Write

From a `Molecule` back to a SMILES string, given a *rank* on the atoms that
says where to start and which neighbor to visit first.  Two passes, as in
every SMILES writer since Weininger (1989):

1. `dfs` walks a spanning forest, visiting neighbors in rank order, and
   records the bonds it meets that lead back to an already-visited atom — the
   ring closures.
2. `emit` writes the forest: the atom, its ring-closure digits (lowest free
   digit at the opening, freed at the closing), then every child but the last
   in parentheses.

With the identity rank, `toSmiles` writes the molecule in its stored atom
order; with `canonicalRanks` (`LeanSMILES.SMILES.Canon`) it writes the
canonical SMILES.  Everything the writer decides it decides from ranks and
bond kinds alone, so when the ranks are label-independent, so is the string.

Tetrahedral marks are not copied from the input but computed: a centre's
neighbors are listed in the order this walk writes them (`listedLigands`, the
parser's convention), and the mark is `@` exactly when that listing is the
stored configuration (`Tetra.isAnticlockwise`).  Other chirality classes are
written as recorded.

Cis/trans marks are computed the same way: the `/` `\` recorded on the bonds
are ignored, and for each stereo double bond, in the order the string reaches
them, one single bond at each end gets a direction that makes the parser read
back the stored arrangement (`cisTransDirs`). Neighboring double bonds of a
conjugated chain share the single bond between them, so a mark already placed
is reused.
-/

@[expose] public section

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

/-! ### Tetrahedral marks -/

/-- The ligands of `a` in the order the string lists them: the atom it is
reached from, its hydrogen (when it has exactly one), its ring-closure partners
in digit order, its children; a lone pair last when three atoms and no
hydrogen are listed.  The parser reads `@`/`@@` against this same order
(`SMILES.State.ligandsOf`). -/
def listedLigands (m : Molecule n) (a : Fin n) (parent : Option (Fin n))
    (rings kids : List (Fin n)) : List (Option (Fin n)) :=
  let h := (m.atom a).totalH
  let listed := parent.toList.map some ++ (if h = 1 then [none] else []) ++ rings.map some ++
    kids.map some
  if listed.length = 3 ∧ h = 0 then listed ++ [none] else listed

/-- Atom `a` carrying the mark of its configuration for the listing `ligands`:
`@` if the listing is the configuration, `@@` if its mirror image, no mark
otherwise. -/
def markedAtom (m : Molecule n) (a : Fin n) (ligands : List (Option (Fin n))) : Atom :=
  match m.stereo[a], Ligands.ofList? ligands with
  | some (.tetra t), some o =>
    if t.isAnticlockwise o then { m.atom a with chirality := some .anticlockwise }
    else if t.isAnticlockwise (o ∘ Ligands.swapLast) then
      { m.atom a with chirality := some .clockwise }
    else m.atom a
  | _, _ => m.atom a

/-! ### Cis/trans marks -/

/-- The atoms in the order the string writes them: each tree in preorder,
children in walk order. -/
def preorder (w : Walk n) : ℕ → List (Fin n) → List (Fin n)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, a :: rest => a :: preorder w fuel (w.children[a] ++ rest)

/-- The flag a direction `d` on the bond between `e` and `s`, written from the
earlier of the two, gives `s` seen from `e` (`SMILES.dirFlagAt`). -/
def flagOf (pos : Vector ℕ n) (e s : Fin n) (d : BondDir) : Bool :=
  if pos[e] < pos[s] then d != .up else d == .up

/-- The direction that gives `s` the flag `f` seen from `e`. -/
def dirFor (pos : Vector ℕ n) (e s : Fin n) (f : Bool) : BondDir :=
  if pos[e] < pos[s] then (if f then .down else .up) else (if f then .up else .down)

/-- The direction `dirFor` chooses gives the flag it was asked for. -/
lemma flagOf_dirFor (pos : Vector ℕ n) (e s : Fin n) (f : Bool) :
    flagOf pos e s (dirFor pos e s f) = f := by
  by_cases h : pos[e] < pos[s] <;> cases f <;> simp only [flagOf, dirFor, h, if_true,
    if_false, Bool.false_eq_true] <;> decide

/-- Directions for single bonds around the stereo double bonds such that the
parser reads back each arrangement: double bonds in the order the string
reaches them, one marked substituent per end — reusing a mark a neighbor
already placed, otherwise the end's first substituent — with flags equal
exactly when the two substituents are cis. -/
def cisTransDirs (m : Molecule n) (pos : Vector ℕ n) : List (Sym2 (Fin n) × BondDir) :=
  let first (b : Bond n) : ℕ := min pos[b.src] pos[b.dst]
  let dbs := (m.bonds.filter fun b ↦
      b.kind == .double && m.stereo[b.src].any Stereo.isPlanar).mergeSort
    fun b c ↦ first b ≤ first c
  dbs.foldl (init := []) fun dirs b ↦
    match m.stereo[b.src] with
    | some (.planar p) =>
      let (x, y) := if pos[b.src] ≤ pos[b.dst] then (b.src, b.dst) else (b.dst, b.src)
      -- the substituents a mark can go on: single bonds a reader takes as single
      let subs (e o : Fin n) : List (Fin n) :=
        (((m.bondsAt e).filter fun c ↦ c.other e != o && c.kind == .single &&
            !((m.atom e).aromatic && (m.atom (c.other e)).aromatic)).map (·.other e)).mergeSort
          fun a c ↦ pos[a] ≤ pos[c]
      let fixed (e o : Fin n) : Option (Fin n × Bool) :=
        (subs e o).findSome? fun s ↦ (dirs.lookup s(e, s)).map fun d ↦ (s, flagOf pos e s d)
      match subs x y, subs y x with
      | sx :: _, sy :: _ =>
        match fixed x y, fixed y x with
        | some _, some _ => dirs
        | some (s, f), none =>
          (s(y, sy), dirFor pos y sy (if p.cis (some s) (some sy) then f else !f)) :: dirs
        | none, some (t, g) =>
          (s(x, sx), dirFor pos x sx (if p.cis (some sx) (some t) then g else !g)) :: dirs
        | none, none =>
          (s(x, sx), dirFor pos x sx true) ::
            (s(y, sy), dirFor pos y sy (p.cis (some sx) (some sy))) :: dirs
      | _, _ => dirs
    | _ => dirs

/-- The symbol for the bond `b` from `a`: its direction mark if it has one,
otherwise the kind as `bondSymbol` writes it. -/
def bondSymbolAt (m : Molecule n) (dirs : List (Sym2 (Fin n) × BondDir)) (a : Fin n)
    (b : Bond n) : String :=
  match dirs.lookup b.edge with
  | some d => d.toChar.toString
  | none => bondSymbol (m.atom a) (m.atom (b.other a)) b.kind

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

/-- Write the ring-closure digits at `a`, a bond symbol at the opening one. -/
def emitClosures (m : Molecule n) (dirs : List (Sym2 (Fin n) × BondDir)) (a : Fin n)
    (cls : List (Bond n)) (e : Emit n) : Emit n :=
  cls.foldl (init := e) fun e c ↦
    match e.opened.lookup c.edge with
    | some d => { out := e.out ++ ringDigit d, opened := e.opened.filter (·.1 != c.edge) }
    | none =>
      let d := freeDigit (e.opened.map (·.2))
      { out := e.out ++ m.bondSymbolAt dirs a c ++ ringDigit d,
        opened := (c.edge, d) :: e.opened }

/-- Write the subtree at `a`. -/
def emit (m : Molecule n) (rank : Fin n → ℕ) (w : Walk n) (dirs : List (Sym2 (Fin n) × BondDir)) :
    ℕ → Fin n → Emit n → Emit n
  | 0, _, e => e
  | fuel + 1, a, e =>
    let cls := (w.closures.filter (·.touches a)).mergeSort fun b c ↦
      rankLE rank (b.other a) (c.other a)
    let kids := w.children[a]
    let ligands := m.listedLigands a w.parent[a] (cls.map (·.other a)) kids
    let e := { e with out := e.out ++ (m.markedAtom a ligands).toSmiles }
    let e := emitClosures m dirs a cls e
    let numKids := kids.length
    kids.zipIdx.foldl (init := e) fun e ⟨o, k⟩ ↦
      let sym := match m.bondBetween a o with
        | some b => m.bondSymbolAt dirs a b
        | none => ""
      if k + 1 < numKids then
        let e' := emit m rank w dirs fuel o { e with out := e.out ++ "(" ++ sym }
        { e' with out := e'.out ++ ")" }
      else emit m rank w dirs fuel o { e with out := e.out ++ sym }

/-- Write the molecule, starting each component at its lowest-ranked atom and
visiting neighbors in rank order; components are joined by `.` in order of
their start atom. -/
def write (m : Molecule n) (rank : Fin n → ℕ) : String :=
  let order := (List.finRange n).mergeSort (rankLE rank)
  let ⟨w, roots⟩ := order.foldl (init := ((Walk.init : Walk n), ([] : List (Fin n))))
    fun ⟨w, roots⟩ s ↦
      if w.visited[s] then (w, roots) else (dfs m rank (n + 1) s w, roots ++ [s])
  let pos : Vector ℕ n := (preorder w (n + 1) roots).zipIdx.foldl (init := Vector.replicate n 0)
    fun v ⟨a, k⟩ ↦ v.set a.val k a.isLt
  let dirs := m.cisTransDirs pos
  let e := roots.foldl (init := (⟨"", []⟩ : Emit n)) fun e r ↦
    let e := if e.out.isEmpty then e else { e with out := e.out ++ "." }
    emit m rank w dirs (n + 1) r e
  e.out

/-- The molecule written in its stored atom order. -/
def toSmiles (m : Molecule n) : String := m.write (·.val)

end LeanSMILES.Molecule

namespace LeanSMILES

/-- A bundled molecule written in its stored atom order. -/
def Mol.toSmiles (M : Mol) : String := M.mol.toSmiles

end LeanSMILES
