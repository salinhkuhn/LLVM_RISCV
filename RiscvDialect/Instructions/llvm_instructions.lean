import RiscvDialect.RDialect
import RiscvDialect.RefinementDialect
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.LLVM.PrettyEDSL
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForLean
import Lean

/-- this file contains a collection of llvm programs that each modell one instruction. 

-/

def llvm_add :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add  %X, %Y : i64
      llvm.return %v1 : i64
  }]

def llvm_sub :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.sub  %X, %Y : i64
      llvm.return %v1 : i64
  }]

def llvm_ret:=
  [llvm(64)| {
    ^bb0(%X : i64):
    llvm.return %X : i64
  }]
