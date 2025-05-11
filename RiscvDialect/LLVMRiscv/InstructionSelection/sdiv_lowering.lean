import RiscvDialect.LLVMRiscv.LLVMAndRiscV
import RiscvDialect.LLVMRiscv.Refinement
import RiscvDialect.LLVMRiscv.Cast

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V

/-! # SDIV no exact   -/

def sdiv_llvm_no_exact : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sdiv  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]
-- at the moment unsure how the conversion cast will eliminate
def sdiv_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%reg1: i64, %reg2: i64 ):
      %0 = "builtin.unrealized_conversion_cast"(%reg1) : (i64) -> !i64
      %1 = "builtin.unrealized_conversion_cast"(%reg2) : (i64) -> !i64
      %2 = div  %0, %1 : !i64 -- value depends on wether to no overflow flag is present or not
      %3 = "builtin.unrealized_conversion_cast" (%2) : (!i64) -> (i64)
      llvm.return %3 : i64
  }]

def llvm_sdiv_lower_riscv_no_flag: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := sdiv_llvm_no_exact , rhs := sdiv_riscv, correct := by
    unfold sdiv_llvm_no_exact sdiv_riscv
    simp_peephole
    simp [LLVM.sdiv,builtin.unrealized_conversion_cast.LLVMToriscv, builtin.unrealized_conversion_cast.riscvToLLVM ]
    rintro (_|x1) (_|x2) <;> simp
    · split
      · simp
      · simp [LLVM.sdiv?,pure_semantics.DIV_pure64_signed_bv]
        by_cases onX2 :  x2 = 0#64
        · simp [onX2]
        · simp [onX2]
          by_cases h:  x1 = BitVec.intMin 64 ∧ x2 = 18446744073709551615#64
          · simp [h]
          · simp [h]
     }

/-! # SDIV exact   -/
def sdiv_llvm_exact : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sdiv exact %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def llvm_sdiv_lower_riscv_exact : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := sdiv_llvm_exact , rhs := sdiv_riscv, correct := by
    unfold sdiv_llvm_exact sdiv_riscv
    simp_peephole
    simp [builtin.unrealized_conversion_cast.LLVMToriscv, builtin.unrealized_conversion_cast.riscvToLLVM,LLVM.sdiv]
    rintro (_|x1) (_|x2)
    · simp [BitVec.Refinement]
    · simp
    · simp
    · simp
      split
      · simp
      · simp [LLVM.sdiv?]
        split
        · case  some.some.isFalse.isTrue ht =>
            simp
        · case  some.some.isFalse.isFalse hf =>
            simp [pure_semantics.DIV_pure64_signed_bv]
            simp at hf
            simp [hf]
    }
