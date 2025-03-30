
import SSA.Core.Tactic
import SSA.Core.ErasedContext
import SSA.Core.HVector
import SSA.Core.EffectKind
import SSA.Core.Util
import RiscvDialect.RDialect
import SSA.Projects.InstCombine.LLVM.PrettyEDSL
--import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForLean
import Lean
import Mathlib.Logic.Function.Iterate
import SSA.Core.Framework
import SSA.Core.Tactic
import SSA.Core.Util
import SSA.Core.MLIRSyntax.GenericParser
import SSA.Core.MLIRSyntax.EDSL
import SSA.Projects.InstCombine.Tactic
import Mathlib.Tactic.Ring

open RV64
open toRISCV -- the riscv dialect

def RiscvInstrSeqRefines (x y : BitVec 64) : Prop := x = y
-- target is a refinement of source
infix:50 (priority:=low) " ⊑ᵣ" => RiscvInstrSeqRefines

-- technically an overkill because its equality but it looks nicer
abbrev Com.RefinementRiscv (src tgt : Com RV64 Γ .pure t)
    (h : RV64TyDenote.toType t = BitVec 64 := by rfl) : Prop :=
  ∀ Γv, (h ▸ src.denote Γv) ⊑ᵣ (h ▸ tgt.denote Γv) -- in they end they must yield the same register value

  
infixr:90 " ⊑ᵣ"  => Com.RefinementRiscv --applies this function so just an infix operator
