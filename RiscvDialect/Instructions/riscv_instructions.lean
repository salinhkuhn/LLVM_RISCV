import RiscvDialect.RefinementDialect
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.LLVM.PrettyEDSL
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForLean
import Lean
import RiscvDialect.RISCV64.Syntax
import RiscvDialect.RISCV64.Base
import RiscvDialect.RISCV64.Semantics

open RISCV64

/-- this file contains a collection of RISCV instructions modelled as computations where each computation contains
one instruction-/

def riscv_add :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.add" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]

def riscv_sub :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.sub" (%Y, %X ) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]

def rhs_riscv_ret :=
  [RV64_com| {
  ^entry (%0 : !i64 ):
    "return" (%0) : ( !i64 ) -> ()
}]
