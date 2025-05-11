import RiscvDialect.LLVMRiscv.LLVMAndRiscV
import RiscvDialect.LLVMRiscv.Refinement
import RiscvDialect.LLVMRiscv.Cast

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V

/-! # UDIV no exact  -/

def udiv_llvm_no_exact : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.udiv  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def udiv_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%reg1: i64, %reg2: i64 ):
      %0 = "builtin.unrealized_conversion_cast"(%reg1) : (i64) -> !i64
      %1 = "builtin.unrealized_conversion_cast"(%reg2) : (i64) -> !i64
      %2 = divu  %0, %1 : !i64 -- value depends on wether to no overflow flag is present or not
      %3 = "builtin.unrealized_conversion_cast" (%2) : (!i64) -> (i64)
      llvm.return %3 : i64
  }]


def llvm_udiv_lower_riscv_no_flag: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := udiv_llvm_no_exact , rhs := udiv_riscv, correct := by
      unfold udiv_llvm_no_exact udiv_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      simp [Option.isSome]
      rintro (_|a) (_|b)
      . simp [LLVM.udiv, BitVec.Refinement,builtin.unrealized_conversion_cast.riscvToLLVM]
      . simp [LLVM.udiv, BitVec.Refinement,builtin.unrealized_conversion_cast.riscvToLLVM]
      . simp [LLVM.udiv, BitVec.Refinement,builtin.unrealized_conversion_cast.riscvToLLVM]
      . simp [LLVM.udiv, BitVec.Refinement,builtin.unrealized_conversion_cast.riscvToLLVM]
        split
        case some.some.h_1 h1 =>
          simp [pure_semantics.DIV_pure64_unsigned_bv]
          by_cases onB : b = 0#64
          · simp [onB]
            split
            case pos.isTrue =>
              simp [LLVM.udiv?]
            case pos.isFalse =>
              simp
          · simp [onB]
            split
            · simp [LLVM.udiv?, pure_semantics.DIV_pure64_unsigned_bv]
              simp [onB]
            · simp
        case some.some.h_2 h2 =>
          split
          · simp
          · simp [LLVM.udiv?, pure_semantics.DIV_pure64_unsigned_bv]
            by_cases onB : (b = 0#64)
            · simp [onB]
            · simp [onB]
      }

/-! # UDIV exact   -/

def udiv_llvm_exact : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %0 = llvm.udiv exact  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %0 : i64
  }]

def llvm_udiv_lower_riscv_flag: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := udiv_llvm_exact , rhs := udiv_riscv, correct := by
      unfold udiv_llvm_exact udiv_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|a) (_|b)
      . simp [LLVM.udiv]
      . simp [LLVM.udiv]
      . simp [LLVM.udiv]
      . simp [LLVM.udiv]
        split
        case some.some.isTrue =>
          simp
        case some.some.isFalse =>
          simp [LLVM.udiv?, pure_semantics.DIV_pure64_unsigned_bv]
          split <;> simp
       }
