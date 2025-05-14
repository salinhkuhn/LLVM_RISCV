// run : lake exec opt2 --passriscv64 test_pipeline/bb2.mlir > output2.mlir
{
  ^entry(%0 : LLVMRiscV.Ty.llvm i64):
    %1 = LLVMRiscV.Op.riscv (RISCV64.Op.li 2) : () → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %2 = LLVMRiscV.Op.riscv (RISCV64.Op.li 1) : () → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %3 = LLVMRiscV.Op.builtin.unrealized_conversion_cast.LLVMToriscv (%0) : (LLVMRiscV.Ty.llvm
      i64) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %4 = LLVMRiscV.Op.riscv
      (RISCV64.Op.and) (%3, %1) : (LLVMRiscV.Ty.riscv
      (RISCV64.Ty.bv), LLVMRiscV.Ty.riscv (RISCV64.Ty.bv)) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %5 = LLVMRiscV.Op.riscv
      (RISCV64.Op.sll) (%4, %2) : (LLVMRiscV.Ty.riscv
      (RISCV64.Ty.bv), LLVMRiscV.Ty.riscv (RISCV64.Ty.bv)) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %6 = LLVMRiscV.Op.builtin.unrealized_conversion_cast.LLVMToriscv (%0) : (LLVMRiscV.Ty.llvm
      i64) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %7 = LLVMRiscV.Op.riscv
      (RISCV64.Op.or) (%5, %6) : (LLVMRiscV.Ty.riscv
      (RISCV64.Ty.bv), LLVMRiscV.Ty.riscv (RISCV64.Ty.bv)) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %8 = LLVMRiscV.Op.riscv
      (RISCV64.Op.sub) (%7, %4) : (LLVMRiscV.Ty.riscv
      (RISCV64.Ty.bv), LLVMRiscV.Ty.riscv (RISCV64.Ty.bv)) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %9 = LLVMRiscV.Op.builtin.unrealized_conversion_cast.riscvToLLVM (%8) : (LLVMRiscV.Ty.riscv
      (RISCV64.Ty.bv)) → (LLVMRiscV.Ty.llvm i64)
    return %9 : (LLVMRiscV.Ty.llvm i64) → ()
}
