import RiscvDialect.LLVMRiscv.LLVMAndRiscV
import RiscvDialect.LLVMRiscv.Refinement
import RiscvDialect.LLVMRiscv.Cast

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V


/- # SRL, not exact
logical right shift operation
in LLVM: if exact flag is set, then returns poison if any non zero bit is shifted  -/

def lshr_llvm_no_flag : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %1 = llvm.lshr %x, %amount : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def srl_riscv := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %base = "builtin.unrealized_conversion_cast"(%x) : (i64) -> !i64
      %shamt = "builtin.unrealized_conversion_cast"(%amount) : (i64) -> !i64
       %res = srl %base, %shamt : !i64
       %y= "builtin.unrealized_conversion_cast" (%res) : (!i64) -> (i64)
      llvm.return %y : i64
  }]

/-!
Remove bitvec lemmas from the simp-set that simplify bitvector operations into toNat operations.
Currently, the bit-shift operations all do this. Instead, these should probably be part of
the `toNat` simpset.
-/
attribute [-simp] BitVec.ushiftRight_eq' BitVec.shiftLeft_eq' BitVec.sshiftRight_eq'


def llvm_srl_lower_riscv : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := lshr_llvm_no_flag , rhs := srl_riscv ,
    correct :=  by
      unfold lshr_llvm_no_flag srl_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|x1) (_|x2) <;> simp only [pure_semantics.RTYPE_pure64_RISCV_SRL_bv,LLVM.lshr];
      ·  simp
      ·  simp
      ·  simp
      · simp only [ne_eq, Option.bind_eq_bind, Option.some_bind, Nat.sub_zero, Nat.reduceAdd,
        Option.getD_some]
        split
        · simp
        . simp [LLVM.lshr?]
          split
          .case some.some.isFalse.isTrue ht =>  simp [BitVec.Refinement]
          . case some.some.isFalse.isFalse hf =>
            simp only [BitVec.Refinement.some_some]
            bv_decide

    }

def lshr_llvm_exact : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %1 = llvm.lshr exact %x, %amount : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64 }]


def llvm_srl_lower_riscv_exact : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := lshr_llvm_exact , rhs := srl_riscv ,
    correct :=  by
      unfold lshr_llvm_exact srl_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|x1) (_|x2) <;> simp [pure_semantics.RTYPE_pure64_RISCV_SRL_bv,LLVM.lshr];
      . split
        . simp [BitVec.Refinement.none_left] -- this is the poison case, where llvm returns a poison value but in riscv we ouptut a concret bitvec value for it,
          -- in detail riscv performs the arithemtic shift with the maximum possible shift amount
        . simp [LLVM.lshr?]
          split
          .case some.some.isFalse.isTrue ht =>
            -- riscv returns the logical shift by the amount
            simp [BitVec.Refinement]
          . case some.some.isFalse.isFalse hf =>
            simp only [BitVec.Refinement.some_some]
            bv_decide }
