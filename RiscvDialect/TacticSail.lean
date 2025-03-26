
import RiscvDialect.Dialect
open Lean
open Lean.Elab.Tactic

macro "simp_sail" : tactic =>
  `(tactic|
      (
        simp (config := {failIfUnchanged := false}) only [
            RV64.UTYPE_pure64_lui
          ];
        simp (config := {failIfUnchanged := false}) only [
            V64.UTYPE_pure64_AUIPC
          ];
      )
  )
