import Lean

/-!
# `#test`: visible unit tests

`#test e` evaluates `e`, a `Bool` or a decidable proposition, when the file is elaborated.
On success it shows `✅ e` in the infoview, like an `#eval` cell. On failure it reports
`❌ e` as an error, so `lake build` fails. For `a == b` and `a = b` it also shows both
sides when they can be printed with `repr`.
-/

namespace MetaPrograms

open Lean Elab Command Term Meta

/-- Evaluate a term of type `Bool`. -/
unsafe def evalBoolUnsafe (t : Term) : TermElabM Bool :=
  evalTerm Bool (mkConst ``Bool) t

@[implemented_by evalBoolUnsafe]
opaque evalBool : Term → TermElabM Bool

unsafe def evalStringUnsafe (t : Term) : TermElabM String :=
  evalTerm String (mkConst ``String) t

@[implemented_by evalStringUnsafe]
opaque evalString : Term → TermElabM String

/-- `t` as a `Bool` term: `decide t` if it is a proposition. -/
def asBoolTerm (t : Term) : TermElabM Term := do
  let e ← withoutErrToSorry <| elabTerm t none
  if (← inferType e).isProp then `(decide $t) else `(($t : Bool))

/-- `repr` of a term, if it has a `Repr` instance and evaluates. -/
def showValue (t : Term) : TermElabM (Option String) := do
  try some <$> evalString (← `(toString (repr $t))) catch _ => pure none

syntax (name := testCmd) "#test " term : command

@[command_elab testCmd]
def elabTest : CommandElab
  | stx@`(#test $t) => do
    let ok ← liftTermElabM do evalBool (← asBoolTerm t)
    if ok then logInfoAt stx m!"✅ {t}"
    else
      let details ← liftTermElabM do
        match t with
        | `($a == $b) | `($a = $b) => do
          match ← showValue a, ← showValue b with
          | some va, some vb => pure m!"\n  left:  {va}\n  right: {vb}"
          | _, _ => pure m!""
        | _ => pure m!""
      logErrorAt stx m!"❌ {t}{details}"
  | _ => throwUnsupportedSyntax

end MetaPrograms
