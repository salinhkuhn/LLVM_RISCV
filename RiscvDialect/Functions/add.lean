import RiscvDialect.Dialect
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.LLVM.PrettyEDSL
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForLean
import Lean
import Mathlib.Tactic.Ring
import SSA.Projects.InstCombine.ForLean
import SSA.Projects.InstCombine.LLVM.EDSL
import SSA.Experimental.Bits.Fast.Reflect
import SSA.Experimental.Bits.Fast.MBA
import SSA.Experimental.Bits.FastCopy.Reflect
import SSA.Experimental.Bits.AutoStructs.Tactic
import SSA.Experimental.Bits.AutoStructs.ForLean
import Std.Tactic.BVDecide
import SSA.Core.Tactic.TacBench
import Leanwuzla
import LLVM-RISCV.instructionWithContext

#check add_64

def add_64 :=
  [llvm(64)| {
  ^bb0(%arg0: i64 , %arg1: i64) :
    %0 = llvm.add %arg1, %arg0 overflow<nsw> : i64
    llvm.return %0 : i64
  }].denote

  def context :=
