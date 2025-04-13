import RiscvDialect.RDialect
import RiscvDialect.RefinementDialect
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.LLVM.PrettyEDSL
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForLean
import RiscvDialect.Instructions.riscv_instructions
import RiscvDialect.Instructions.llvm_instructions
import RiscvDialect.Peephole_Optimizations.RISCVRewrites
import Lean

open LLVM



/-- this file contains the function to lower llvm instructions into other llvm instructions.
The purpose of this was to test the design of the translation process. -/

def loweringLLVMToLLVM {Γ : Ctxt LLVM.Ty} (com : Com LLVM Γ .pure (.bitvec 64)) :   Option (Com LLVM Γ .pure (.bitvec 64))  :=
  match Γ, com with
  | _, Com.ret x  =>  some (Com.ret x)
  | _, Com.var (α := InstCombine.Ty.bitvec 64 ) (e) c' =>
        let e' := (transf e) -- map the expression to a riscv expression
        match lowering c' with
        | some com => some (Com.var (e') (com))
        | none => none
  | _, Com.var (α := InstCombine.Ty.bitvec _) _ _ =>
      none
