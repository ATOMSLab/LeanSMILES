import Std.Data.HashMap

/-!
# Storage for `cached def`

The cache cell used by `MetaPrograms/Cache.lean`. It lives in its own module, which is
part of the precompiled `LeanSMILESExec` library: initializers of precompiled modules run
when they are loaded, so the `IO.Ref` below exists before any notebook cell reads it.
-/

namespace MetaPrograms

/-- Values of `cached def`s, each wrapped in a closure `Unit → α` so any type can be
stored uniformly. -/
initialize notebookCache : IO.Ref (Std.HashMap Lean.Name NonScalar) ← IO.mkRef {}

end MetaPrograms
