import RiscvDialect.LLVMRiscv.LLVMAndRiscV
import RiscvDialect.LLVMRiscv.Refinement
import RiscvDialect.LLVMRiscv.Cast

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V

/-! # SUB, no flags   -/

-- done


-- tentative adding pattern fr operand involving only one varible -> maybe generalize tzhis more genrally as a rewrte ?

def llvm_sub_self: Com  LLVMPlusRiscV [.llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64 ): -- adding y to make it compile
      %1 = llvm.sub  %x, %x : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def sub_riscv_self: Com  LLVMPlusRiscV [.llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64):
      %0 = "builtin.unrealized_conversion_cast"(%x) : (i64) -> !i64
      %2 = sub %0, %0 : !i64 -- value depends on wether to no overflow flag is present or not
      %3 = "builtin.unrealized_conversion_cast" (%2) : (!i64) -> (i64)
      llvm.return %3 : i64
  }]

def llvm_sub_lower_riscv_no_flag_self: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_sub_self , rhs := sub_riscv_self, correct := by
        unfold llvm_sub_self sub_riscv_self
        simp_peephole
        sorry
      }




def llvm_sub: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sub  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def sub_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %0 = "builtin.unrealized_conversion_cast"(%x) : (i64) -> !i64
      %1 = "builtin.unrealized_conversion_cast"(%y) : (i64) -> !i64
      %2 = sub %0, %1 : !i64 -- value depends on wether to no overflow flag is present or not
      %3 = "builtin.unrealized_conversion_cast" (%2) : (!i64) -> (i64)
      llvm.return %3 : i64
  }]

def llvm_sub_lower_riscv_no_flag: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_sub , rhs := sub_riscv, correct := by
        unfold llvm_sub sub_riscv
        simp_peephole
        rintro (_|a) (_|b)
        . simp [LLVM.sub]
        . simp [LLVM.sub]
        . simp [LLVM.sub]
        . simp [builtin.unrealized_conversion_cast.riscvToLLVM, builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_SUB]
          simp [LLVM.sub,LLVM.sub?]
      }

/-! # SUB, flags  -/

def llvm_sub_nsw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sub  %x, %y overflow<nsw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def llvm_sub_nsw_lower_riscv: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_sub_nsw , rhs := sub_riscv, correct := by
     unfold llvm_sub_nsw sub_riscv
     simp_peephole
     rintro (_|a) (_|b)
     · simp [builtin.unrealized_conversion_cast.riscvToLLVM, RTYPE_pure64_RISCV_SUB, LLVM.sub ]
     · simp [LLVM.sub ]
     · simp [LLVM.sub]
     · simp [LLVM.sub, builtin.unrealized_conversion_cast.riscvToLLVM, builtin.unrealized_conversion_cast.LLVMToriscv, LLVM.sub?, RTYPE_pure64_RISCV_SUB]
       split
       · simp [BitVec.Refinement]  -- this is the case where LLVM has a signed overflow and therefore returns a poison value.
       · simp  -- this is the case where we do not have signed overflow
  }

def llvm_sub_nuw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sub  %x, %y overflow<nuw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]
-- siubtraction with no unsigned overflow flag
def llvm_sub_nuw_lower_riscv: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_sub_nuw , rhs := sub_riscv, correct := by
    unfold llvm_sub_nuw sub_riscv
    simp_peephole
    rintro (_|a) (_|b) <;> simp only [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_SUB, LLVM.sub ]
    · simp
    · simp
    · simp
    · simp only [Bool.false_eq_true, false_and, ↓reduceIte, true_and, Option.bind_eq_bind,
      Option.some_bind, Option.getD_some, BitVec.sub_eq]
      split -- split on the unsignedOverflow given the nuw flag
      · simp
      · simp[LLVM.sub?]
    }

def llvm_sub_nsw_nuw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sub  %x, %y overflow<nsw, nuw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]
def llvm_sub_nsw_nuw_lower_riscv: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_sub_nsw_nuw , rhs := sub_riscv, correct := by
    unfold llvm_sub_nsw_nuw sub_riscv --unfolding
    simp_peephole -- call simp_peephole function --> need to think how much it depends on the simp_peephole implementation
    rintro (_|a) (_|b) <;> simp only [builtin.unrealized_conversion_cast.riscvToLLVM, builtin.unrealized_conversion_cast.LLVMToriscv,LLVM.sub, RTYPE_pure64_RISCV_SUB ]
    . simp
    . simp
    . simp
    . simp
      split
      · case some.some.isTrue => -- this is the signed subtraction overflow case
          simp [BitVec.Refinement]
      · case some.some.isFalse hf =>
           simp only [Bool.not_eq_true] at hf
           split
           · simp
           · simp [LLVM.sub?]
      }
