open Lean.Parser.Tactic (location)
macro "simp_peephole" "[" ts: Lean.Parser.Tactic.simpLemma,* "]" loc:(location)? : tactic =>
  `(tactic|(
      -- First, we ensure potential quantification over a Valuation is made explicit
      first
      | rw [funext_iff (α := Ctxt.Valuation _)] $[$loc]?
      | change ∀ (_ : Ctxt.Valuation _), _ $[$loc]?
      | skip
      -- Then, we simplify with the `simp_denote` simpset
      simp (config := {failIfUnchanged := false}) only [simp_denote, $ts,*] $[$loc]?
  ))

macro "simp_peephole" loc:(location)?  : tactic => `(tactic | simp_peephole [] $[$loc]?)
/- seemed to work on my examples -/
