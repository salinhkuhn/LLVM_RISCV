import RiscvDialect.LLVMRiscv.InstructionSelection.all

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V

/- # AND -/
def testsimple_llvm :=
  [LV| {
    ^entry (%arg0: i64):
    %0 = llvm.mlir.constant(31 : i64) : i64
    %1 = llvm.add %arg0, %arg0 : i64
    %2 = llvm.xor %1, %arg0  : i64
    %3 = llvm.mul %2, %2 : i64
    %4 = llvm.or %3, %1  : i64
    %5 = llvm.sub %4, %2 : i64
    %6 = llvm.xor %5, %arg0  : i64
    %7 = llvm.add %6, %1 : i64
    %8 = llvm.mul %7, %0 : i64
    %9 = llvm.or %8, %2  : i64
    %10 = llvm.sub %9, %6 : i64
    llvm.return %10 : i64
  }]


def llvm_and_lower_riscv1 : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs:= and_llvm , rhs:= and_riscv ,
   correct := by
    unfold and_llvm and_riscv
    simp_peephole
    simp [builtin.unrealized_conversion_cast.riscvToLLVM,  builtin.unrealized_conversion_cast.LLVMToriscv]
    simp [LLVM.and, RTYPE_pure64_RISCV_AND]
    rintro (_|foo) (_|bar)
    · simp
    · simp
  }
