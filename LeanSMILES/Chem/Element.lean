/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Card

/-!
# LeanSMILES.Chem.Element

The chemical elements as a 118-constructor enumeration, in order of atomic
number, so that `atomicNumber` is the constructor index shifted by one and
`Fintype.card Element = 118` is a fact about the type rather than a table.

Everything SMILES needs to know about an element lives here: its symbol (both
directions), whether it may be written bare (the OpenSMILES *organic subset*),
whether it may be written lowercase (aromatic), and the default valences the
implicit-hydrogen rule uses.  The valence table is deliberately the thin
OpenSMILES one — this library aims at a syntactically faithful reading of
SMILES, not at agreeing with any one toolkit's chemistry model on edge cases.

This file is generated (`scratchpad/gen_element.py`) so the three 118-entry
tables cannot drift; edit the generator, not the arms.
-/

namespace LeanSMILES

/-- The 118 chemical elements, in order of atomic number. The SMILES wildcard
`*` is **not** an element; `Atom.element` is an `Option Element` and `*` is
`none`, so that every theorem about `Element` is a theorem about real elements. -/
inductive Element
  | H | He | Li | Be | B | C | N | O | F | Ne
  | Na | Mg | Al | Si | P | S | Cl | Ar | K | Ca
  | Sc | Ti | V | Cr | Mn | Fe | Co | Ni | Cu | Zn
  | Ga | Ge | As | Se | Br | Kr | Rb | Sr | Y | Zr
  | Nb | Mo | Tc | Ru | Rh | Pd | Ag | Cd | In | Sn
  | Sb | Te | I | Xe | Cs | Ba | La | Ce | Pr | Nd
  | Pm | Sm | Eu | Gd | Tb | Dy | Ho | Er | Tm | Yb
  | Lu | Hf | Ta | W | Re | Os | Ir | Pt | Au | Hg
  | Tl | Pb | Bi | Po | At | Rn | Fr | Ra | Ac | Th
  | Pa | U | Np | Pu | Am | Cm | Bk | Cf | Es | Fm
  | Md | No | Lr | Rf | Db | Sg | Bh | Hs | Mt | Ds
  | Rg | Cn | Nh | Fl | Mc | Lv | Ts | Og
  deriving DecidableEq, Repr, Inhabited, Fintype, Ord

namespace Element

/-- Atomic number `Z`: the constructor index shifted by one, so `H.atomicNumber = 1`. -/
def atomicNumber (e : Element) : ℕ := e.ctorIdx + 1

theorem atomicNumber_injective : Function.Injective atomicNumber := by
  intro a b h
  have h' : a.ctorIdx = b.ctorIdx := Nat.succ_injective h
  have := congrArg Element.ofNat h'
  simpa [Element.ofNat_ctorIdx] using this

/-- The element with atomic number `z`, for `1 ≤ z ≤ 118`. -/
def ofAtomicNumber? (z : ℕ) : Option Element :=
  if 1 ≤ z ∧ z ≤ 118 then some (Element.ofNat (z - 1)) else none

lemma card : Fintype.card Element = 118 := by decide

/-- The element's symbol as written in SMILES (and everywhere else). -/
def symbol : Element → String
  | .H => "H"
  | .He => "He"
  | .Li => "Li"
  | .Be => "Be"
  | .B => "B"
  | .C => "C"
  | .N => "N"
  | .O => "O"
  | .F => "F"
  | .Ne => "Ne"
  | .Na => "Na"
  | .Mg => "Mg"
  | .Al => "Al"
  | .Si => "Si"
  | .P => "P"
  | .S => "S"
  | .Cl => "Cl"
  | .Ar => "Ar"
  | .K => "K"
  | .Ca => "Ca"
  | .Sc => "Sc"
  | .Ti => "Ti"
  | .V => "V"
  | .Cr => "Cr"
  | .Mn => "Mn"
  | .Fe => "Fe"
  | .Co => "Co"
  | .Ni => "Ni"
  | .Cu => "Cu"
  | .Zn => "Zn"
  | .Ga => "Ga"
  | .Ge => "Ge"
  | .As => "As"
  | .Se => "Se"
  | .Br => "Br"
  | .Kr => "Kr"
  | .Rb => "Rb"
  | .Sr => "Sr"
  | .Y => "Y"
  | .Zr => "Zr"
  | .Nb => "Nb"
  | .Mo => "Mo"
  | .Tc => "Tc"
  | .Ru => "Ru"
  | .Rh => "Rh"
  | .Pd => "Pd"
  | .Ag => "Ag"
  | .Cd => "Cd"
  | .In => "In"
  | .Sn => "Sn"
  | .Sb => "Sb"
  | .Te => "Te"
  | .I => "I"
  | .Xe => "Xe"
  | .Cs => "Cs"
  | .Ba => "Ba"
  | .La => "La"
  | .Ce => "Ce"
  | .Pr => "Pr"
  | .Nd => "Nd"
  | .Pm => "Pm"
  | .Sm => "Sm"
  | .Eu => "Eu"
  | .Gd => "Gd"
  | .Tb => "Tb"
  | .Dy => "Dy"
  | .Ho => "Ho"
  | .Er => "Er"
  | .Tm => "Tm"
  | .Yb => "Yb"
  | .Lu => "Lu"
  | .Hf => "Hf"
  | .Ta => "Ta"
  | .W => "W"
  | .Re => "Re"
  | .Os => "Os"
  | .Ir => "Ir"
  | .Pt => "Pt"
  | .Au => "Au"
  | .Hg => "Hg"
  | .Tl => "Tl"
  | .Pb => "Pb"
  | .Bi => "Bi"
  | .Po => "Po"
  | .At => "At"
  | .Rn => "Rn"
  | .Fr => "Fr"
  | .Ra => "Ra"
  | .Ac => "Ac"
  | .Th => "Th"
  | .Pa => "Pa"
  | .U => "U"
  | .Np => "Np"
  | .Pu => "Pu"
  | .Am => "Am"
  | .Cm => "Cm"
  | .Bk => "Bk"
  | .Cf => "Cf"
  | .Es => "Es"
  | .Fm => "Fm"
  | .Md => "Md"
  | .No => "No"
  | .Lr => "Lr"
  | .Rf => "Rf"
  | .Db => "Db"
  | .Sg => "Sg"
  | .Bh => "Bh"
  | .Hs => "Hs"
  | .Mt => "Mt"
  | .Ds => "Ds"
  | .Rg => "Rg"
  | .Cn => "Cn"
  | .Nh => "Nh"
  | .Fl => "Fl"
  | .Mc => "Mc"
  | .Lv => "Lv"
  | .Ts => "Ts"
  | .Og => "Og"

/-- Parse an element symbol. Case-sensitive: aromatic lowercase symbols are
handled by the SMILES tokenizer, which capitalises before calling this. -/
def ofSymbol? : String → Option Element
  | "H" => some .H
  | "He" => some .He
  | "Li" => some .Li
  | "Be" => some .Be
  | "B" => some .B
  | "C" => some .C
  | "N" => some .N
  | "O" => some .O
  | "F" => some .F
  | "Ne" => some .Ne
  | "Na" => some .Na
  | "Mg" => some .Mg
  | "Al" => some .Al
  | "Si" => some .Si
  | "P" => some .P
  | "S" => some .S
  | "Cl" => some .Cl
  | "Ar" => some .Ar
  | "K" => some .K
  | "Ca" => some .Ca
  | "Sc" => some .Sc
  | "Ti" => some .Ti
  | "V" => some .V
  | "Cr" => some .Cr
  | "Mn" => some .Mn
  | "Fe" => some .Fe
  | "Co" => some .Co
  | "Ni" => some .Ni
  | "Cu" => some .Cu
  | "Zn" => some .Zn
  | "Ga" => some .Ga
  | "Ge" => some .Ge
  | "As" => some .As
  | "Se" => some .Se
  | "Br" => some .Br
  | "Kr" => some .Kr
  | "Rb" => some .Rb
  | "Sr" => some .Sr
  | "Y" => some .Y
  | "Zr" => some .Zr
  | "Nb" => some .Nb
  | "Mo" => some .Mo
  | "Tc" => some .Tc
  | "Ru" => some .Ru
  | "Rh" => some .Rh
  | "Pd" => some .Pd
  | "Ag" => some .Ag
  | "Cd" => some .Cd
  | "In" => some .In
  | "Sn" => some .Sn
  | "Sb" => some .Sb
  | "Te" => some .Te
  | "I" => some .I
  | "Xe" => some .Xe
  | "Cs" => some .Cs
  | "Ba" => some .Ba
  | "La" => some .La
  | "Ce" => some .Ce
  | "Pr" => some .Pr
  | "Nd" => some .Nd
  | "Pm" => some .Pm
  | "Sm" => some .Sm
  | "Eu" => some .Eu
  | "Gd" => some .Gd
  | "Tb" => some .Tb
  | "Dy" => some .Dy
  | "Ho" => some .Ho
  | "Er" => some .Er
  | "Tm" => some .Tm
  | "Yb" => some .Yb
  | "Lu" => some .Lu
  | "Hf" => some .Hf
  | "Ta" => some .Ta
  | "W" => some .W
  | "Re" => some .Re
  | "Os" => some .Os
  | "Ir" => some .Ir
  | "Pt" => some .Pt
  | "Au" => some .Au
  | "Hg" => some .Hg
  | "Tl" => some .Tl
  | "Pb" => some .Pb
  | "Bi" => some .Bi
  | "Po" => some .Po
  | "At" => some .At
  | "Rn" => some .Rn
  | "Fr" => some .Fr
  | "Ra" => some .Ra
  | "Ac" => some .Ac
  | "Th" => some .Th
  | "Pa" => some .Pa
  | "U" => some .U
  | "Np" => some .Np
  | "Pu" => some .Pu
  | "Am" => some .Am
  | "Cm" => some .Cm
  | "Bk" => some .Bk
  | "Cf" => some .Cf
  | "Es" => some .Es
  | "Fm" => some .Fm
  | "Md" => some .Md
  | "No" => some .No
  | "Lr" => some .Lr
  | "Rf" => some .Rf
  | "Db" => some .Db
  | "Sg" => some .Sg
  | "Bh" => some .Bh
  | "Hs" => some .Hs
  | "Mt" => some .Mt
  | "Ds" => some .Ds
  | "Rg" => some .Rg
  | "Cn" => some .Cn
  | "Nh" => some .Nh
  | "Fl" => some .Fl
  | "Mc" => some .Mc
  | "Lv" => some .Lv
  | "Ts" => some .Ts
  | "Og" => some .Og
  | _ => none

instance : ToString Element := ⟨symbol⟩

/-- Every element, in atomic-number order. -/
def all : List Element :=
  [
   .H, .He, .Li, .Be, .B, .C, .N, .O, .F, .Ne, .Na, .Mg,
   .Al, .Si, .P, .S, .Cl, .Ar, .K, .Ca, .Sc, .Ti, .V, .Cr,
   .Mn, .Fe, .Co, .Ni, .Cu, .Zn, .Ga, .Ge, .As, .Se, .Br, .Kr,
   .Rb, .Sr, .Y, .Zr, .Nb, .Mo, .Tc, .Ru, .Rh, .Pd, .Ag, .Cd,
   .In, .Sn, .Sb, .Te, .I, .Xe, .Cs, .Ba, .La, .Ce, .Pr, .Nd,
   .Pm, .Sm, .Eu, .Gd, .Tb, .Dy, .Ho, .Er, .Tm, .Yb, .Lu, .Hf,
   .Ta, .W, .Re, .Os, .Ir, .Pt, .Au, .Hg, .Tl, .Pb, .Bi, .Po,
   .At, .Rn, .Fr, .Ra, .Ac, .Th, .Pa, .U, .Np, .Pu, .Am, .Cm,
   .Bk, .Cf, .Es, .Fm, .Md, .No, .Lr, .Rf, .Db, .Sg, .Bh, .Hs,
   .Mt, .Ds, .Rg, .Cn, .Nh, .Fl, .Mc, .Lv, .Ts, .Og
  ]

/-- The OpenSMILES *organic subset*: the elements that may be written without
brackets, whose hydrogen count is then implied by `defaultValences`. -/
def inOrganicSubset : Element → Bool
  | .B | .C | .N | .O | .P | .S | .F | .Cl | .Br | .I => true
  | _ => false

/-- The elements OpenSMILES allows to carry a lowercase (aromatic) symbol. -/
def aromaticAllowed : Element → Bool
  | .B | .C | .N | .O | .P | .S | .Se | .As => true
  | _ => false

/-- OpenSMILES default valences, ascending, for the organic subset; `[]` for
every other element, which therefore never receives implicit hydrogens. -/
def defaultValences : Element → List ℕ
  | .B => [3]
  | .C => [4]
  | .N => [3, 5]
  | .O => [2]
  | .P => [3, 5]
  | .S => [2, 4, 6]
  | .F | .Cl | .Br | .I => [1]
  | _ => []

end Element

end LeanSMILES
