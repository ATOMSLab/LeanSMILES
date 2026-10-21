import Lean
import LeanSMILES.MetaPrograms.CacheStore

/-!
# `cached def`: notebook variables

In a Jupyter notebook, `model = train(...)` runs once and later cells reuse the result.
A Lean `def` is recomputed every time an `#eval` uses it. `cached def` gives `def`s the
notebook behaviour:

```
cached def model : ML.Exec.LinearModel 2048 := ML.Exec.linRegGD cfg split.train
```

* `model` is a normal definition with body `ML.Exec.linRegGD cfg split.train`. It is
  `@[irreducible]`, so type checking never tries to evaluate it (which matters when types
  mention values like `records.size`), but proofs can still `unfold` it.
* When the command is elaborated, the body is evaluated once (with compiled code) and the
  value is stored in a cache. Through `implemented_by`, every later `#eval` or `#test`
  that uses `model` reads the stored value instead of recomputing it.

Re-elaborating the command (editing the cell) recomputes and replaces the stored value.
-/

namespace MetaPrograms

open Lean Elab Command Term Meta

/-- Read a cached value (used by the `implemented_by` readers). -/
@[noinline] unsafe def cacheGet (α : Type) (n : Name) : α :=
  match unsafeBaseIO (notebookCache.get) |>.get? n with
  | some boxed => (unsafeCast boxed : Unit → α) ()
  | none =>
    have : Inhabited α := ⟨unsafeCast ()⟩
    panic! s!"cached def {n}: no cached value (re-elaborate its definition)"

unsafe def evalBoxedUnsafe (t : Term) : TermElabM (IO NonScalar) :=
  evalTerm (IO NonScalar) (mkApp (mkConst ``IO) (mkConst ``NonScalar)) t (safety := .unsafe)

@[implemented_by evalBoxedUnsafe]
opaque evalBoxed : Term → TermElabM (IO NonScalar)

/-- `cached def x : T := e` — a definition whose value is computed once (see the module
docstring). -/
syntax (name := cachedDef) "cached " "def " ident " : " term " := " term : command

@[command_elab cachedDef]
def elabCachedDef : CommandElab
  | `(cached def $x:ident : $ty := $val) => do
    let declName := (← getCurrNamespace) ++ x.getId
    let reader := mkIdent (x.getId ++ `_cached)
    elabCommand (← `(unsafe def $reader : $ty := MetaPrograms.cacheGet $ty $(quote declName)))
    elabCommand (← `(@[implemented_by $reader, irreducible] def $x : $ty := $val))
    -- evaluate the body once; binding it with `>>=` forces it before the closure is built
    let compute ← liftTermElabM <| evalBoxed (← `(
      (pure ($val : $ty) : IO $ty) >>= fun v =>
        pure (unsafeCast (fun (_ : Unit) => v) : NonScalar)))
    let boxed ← compute
    notebookCache.modify (·.insert declName boxed)
  | _ => throwUnsupportedSyntax

end MetaPrograms
