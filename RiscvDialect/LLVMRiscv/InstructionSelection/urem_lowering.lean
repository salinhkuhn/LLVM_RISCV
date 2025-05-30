import RiscvDialect.LLVMRiscv.LLVMAndRiscV
import RiscvDialect.LLVMRiscv.Refinement
import RiscvDialect.LLVMRiscv.Cast

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V

/-! # UREM I need help  -/
/-
	udiv	x8, x0, x1
	msub	x0, x8, x1, x0
-/

def llvm_urem: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.urem  %x, %y : i64
      llvm.return %1 : i64
  }]

def urem_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%reg1: i64, %reg2: i64 ):
      %0 = "builtin.unrealized_conversion_cast"(%reg1) : (i64) -> !i64
      %1 = "builtin.unrealized_conversion_cast"(%reg2) : (i64) -> !i64
      %2 = remu %0, %1 : !i64 -- value depends on wether to no overflow flag is present or not
      %3 = "builtin.unrealized_conversion_cast" (%2) : (!i64) -> (i64)
      llvm.return %3 : i64
  }]

  def llvm_urem_lower_riscv: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_urem , rhs := urem_riscv, correct := by
    unfold llvm_urem urem_riscv
    simp_peephole
    rintro (_|a) (_|b) <;> simp only [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv, BitVec.Refinement, LLVM.urem]
    . simp
    . simp
    . simp
    . simp [BitVec.Refinement , RTYPE_pure64_RISCV_XOR , builtin.unrealized_conversion_cast.riscvToLLVM, builtin.unrealized_conversion_cast.LLVMToriscv]
      simp [LLVM.urem?]
      split
      .case some.some.isTrue ht => /- Taking the remainder of a division by zero is undefined behavior -/
        simp [BitVec.Refinement]
      .case some.some.isFalse hf =>
        simp[pure_semantics.REM_pure64_unsigned_bv]
        simp [hf]
  }
