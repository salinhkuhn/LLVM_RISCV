import RiscvDialect.LLVMRiscv.LLVMAndRiscV
import RiscvDialect.LLVMRiscv.Refinement
import RiscvDialect.LLVMRiscv.Cast

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V

/-! # REM -/
/-- This file contains the lowerings for the llm rem instruction.
We take the diffrent possible flags into account. -/

def rem_llvm : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.srem %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def rem_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%reg1: i64, %reg2: i64 ):
      %0 = "builtin.unrealized_conversion_cast"(%reg1) : (i64) -> !i64
      %1 = "builtin.unrealized_conversion_cast"(%reg2) : (i64) -> !i64
      %2 = rem  %0, %1 : !i64 -- value depends on wether to no overflow flag is present or not
      %3 = "builtin.unrealized_conversion_cast" (%2) : (!i64) -> (i64)
      llvm.return %3 : i64
  }]

def llvm_rem_lower_riscv : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := rem_llvm , rhs := rem_riscv,
    correct :=  by
      unfold rem_llvm rem_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|x1) (_|x2) <;> simp [REM_pure64_signed, LLVM.srem, LLVM.srem?,pure_semantics.REM_pure64_signed_bv]
      split -- poison if reminder by zero or int min reminder by -1
      · simp
      · simp
  }
