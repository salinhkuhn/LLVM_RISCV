import RiscvDialect.LLVMRiscv.LLVMAndRiscV
import RiscvDialect.LLVMRiscv.Refinement
import RiscvDialect.LLVMRiscv.Cast

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V
/-! # SHL (shift left) nsw nuw   -/

def shl_llvm: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.shl  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def shl_llvm_nsw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.shl  %x, %y overflow<nsw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def shl_llvm_nuw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.shl  %x, %y overflow<nuw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def shl_llvm_nsw_nuw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.shl  %x, %y overflow<nsw,nuw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

-- at the moment unsure how the conversion cast will eliminate
def shl_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%reg1: i64, %reg2: i64 ):
      %0 = "builtin.unrealized_conversion_cast"(%reg1) : (i64) -> !i64
      %1 = "builtin.unrealized_conversion_cast"(%reg2) : (i64) -> !i64
      %2 = sll  %0, %1 : !i64 -- value depends on wether to no overflow flag is present or not
      %3 = "builtin.unrealized_conversion_cast" (%2) : (!i64) -> (i64)
      llvm.return %3 : i64
  }]

def llvm_shl_lower_riscv: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := shl_llvm , rhs := shl_riscv, correct := by
        unfold shl_llvm shl_riscv
        simp_peephole
        rintro (_|a) (_|b)<;> simp [ builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv, LLVM.shl ]
        simp [ LLVM.shl?,pure_semantics.RTYPE_pure64_RISCV_SLL_bv]
        split
        case some.some.isTrue ht =>
          simp
        case some.some.isFalse hf =>
          simp at hf
          simp
          have hultiff := BitVec.ult_iff_lt (x:= b) (y:= 64#64)
          have hulttonat := BitVec.ult_iff_toNat_lt (x:= b) (y:= 64#64)
          rw [hultiff ] at hulttonat
          simp [hf] at hulttonat
          rw [Nat.mod_eq_of_lt hulttonat]
         }


def llvm_shl_lower_riscv_nsw: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := shl_llvm_nsw , rhs := shl_riscv, correct := by
        unfold shl_llvm_nsw shl_riscv
        simp_peephole
        rintro (_|a) (_|b)<;> simp [ builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv, LLVM.shl ]
        . split
          simp only [LLVM.shl?, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, ge_iff_le,
            BitVec.shiftLeft_eq']
          split
          . case some.some.isTrue.isTrue ht =>  simp [BitVec.Refinement]
          . case some.some.isTrue.isFalse htf =>
            simp only [pure_semantics.RTYPE_pure64_RISCV_SLL_bv]
            simp only [Nat.sub_zero, Nat.reduceAdd, BitVec.shiftLeft_eq', BitVec.extractLsb_toNat,
              Nat.shiftRight_zero, tsub_zero, Nat.reducePow, BitVec.Refinement.some_some]
            simp only [BitVec.not_le] at htf
            rw [Nat.mod_eq]
            simp only [Nat.ofNat_pos, true_and]
            have h: b < 64#64 → b.toNat < 64  := by
              intro e
              bv_omega
            apply h at htf
            split
            · omega
            · simp
          . simp [BitVec.Refinement]
         }

def llvm_shl_lower_riscv_nuw: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := shl_llvm_nuw , rhs := shl_riscv, correct := by
        unfold shl_llvm_nuw shl_riscv
        simp_peephole
        rintro (_|a) (_|b)<;> simp [ builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv, LLVM.shl ]
        split <;> simp [pure_semantics.RTYPE_pure64_RISCV_SLL_bv, LLVM.shl?]
        · split
          case some.some.isTrue.isTrue =>
            simp
          case some.some.isTrue.isFalse hfff =>
            simp
            simp at hfff
            have hultiff := BitVec.ult_iff_lt (x:= b) (y:= 64#64)
            have hulttonat := BitVec.ult_iff_toNat_lt (x:= b) (y:= 64#64)
            rw [hultiff ] at hulttonat
            simp [hfff] at hulttonat
            rw [Nat.mod_eq_of_lt hulttonat] }

def llvm_shl_lower_riscv_nsw_nuw: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := shl_llvm_nsw_nuw , rhs := shl_riscv, correct := by
        unfold shl_llvm_nsw_nuw shl_riscv
        simp_peephole
        rintro (_|a) (_|b)<;> simp [ builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv, LLVM.shl ]
        split
        case some.some.isTrue ht =>
          split
          case isFalse hff =>
            simp
          case isTrue htt  =>
            unfold LLVM.shl? pure_semantics.RTYPE_pure64_RISCV_SLL_bv
            split
            case isTrue httt =>
              simp
            case isFalse hfff =>
              simp at hfff
              simp
              have hultiff := BitVec.ult_iff_lt (x:= b) (y:= 64#64)
              have hulttonat := BitVec.ult_iff_toNat_lt (x:= b) (y:= 64#64)
              rw [hultiff ] at hulttonat
              simp [hfff] at hulttonat
              rw [Nat.mod_eq_of_lt hulttonat]
        case some.some.isFalse hf =>
          simp
      }
