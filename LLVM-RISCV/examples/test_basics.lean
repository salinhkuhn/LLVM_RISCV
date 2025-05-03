import RiscvDialect.LLVMRiscv.InstructionSelection.all

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V

/- # AND -/
def testsimple_llvm :=
  [LV| {
    ^entry (%arg0: i64):
    %0 = llvm.mlir.constant(31 : i64) : i64
    %1 = llvm.add %arg0, %arg0
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

def testsimple_riscv := [LV| {
    ^entry (%a00: i64 ):
      %a0 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%a00) : (i64) -> !i64
      %a1 = li (2) : !i64
      %a1 = add	 a0, a0 : !i64
        %a2 =	xor	 a1, a0
        %a3 = mul	 a2, a2
        %a4 =  a3, a1
        %a5 =	sub	 a4, a2
        %a6 = xor	 a5, a0 -- a3
         %a7 =	add	 a6, a1
         	slli	a3, a7, 0x5
         	sub	a3, a3, a7
          or	a2, a3, a2
         	sub	a0, a2, a0
        	ret
       %addl = "builtin.unrealized_conversion_cast.riscvToLLVM" (%add1) : (!i64) -> (i64)
      llvm.return %addl : i64
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
