// run : lake exec opt2 --passriscv64 test_pipeline/bb0.mlir > output0.mlir
{
  ^entry(%0 : LLVMRiscV.Ty.llvm i64):
    %1 = LLVMRiscV.Op.llvm "llvm.mlir.constant" { value = 20 : i64 } : () → (LLVMRiscV.Ty.llvm i64)
    %2 = LLVMRiscV.Op.llvm "llvm.mlir.constant" { value = 31 : i64 } : () → (LLVMRiscV.Ty.llvm i64)
    %3 = LLVMRiscV.Op.builtin.unrealized_conversion_cast.LLVMToriscv (%0) : (LLVMRiscV.Ty.llvm
      i64) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %4 = LLVMRiscV.Op.builtin.unrealized_conversion_cast.LLVMToriscv (%2) : (LLVMRiscV.Ty.llvm
      i64) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %5 = LLVMRiscV.Op.riscv
      (RISCV64.Op.sra) (%3, %4) : (LLVMRiscV.Ty.riscv
      (RISCV64.Ty.bv), LLVMRiscV.Ty.riscv (RISCV64.Ty.bv)) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %6 = LLVMRiscV.Op.builtin.unrealized_conversion_cast.LLVMToriscv (%1) : (LLVMRiscV.Ty.llvm
      i64) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %7 = LLVMRiscV.Op.riscv
      (RISCV64.Op.and) (%5, %6) : (LLVMRiscV.Ty.riscv
      (RISCV64.Ty.bv), LLVMRiscV.Ty.riscv (RISCV64.Ty.bv)) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %8 = LLVMRiscV.Op.riscv
      (RISCV64.Op.add) (%7, %5) : (LLVMRiscV.Ty.riscv
      (RISCV64.Ty.bv), LLVMRiscV.Ty.riscv (RISCV64.Ty.bv)) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %9 = LLVMRiscV.Op.riscv
      (RISCV64.Op.add) (%8, %7) : (LLVMRiscV.Ty.riscv
      (RISCV64.Ty.bv), LLVMRiscV.Ty.riscv (RISCV64.Ty.bv)) → (LLVMRiscV.Ty.riscv (RISCV64.Ty.bv))
    %10 = LLVMRiscV.Op.builtin.unrealized_conversion_cast.riscvToLLVM (%9) : (LLVMRiscV.Ty.riscv
      (RISCV64.Ty.bv)) → (LLVMRiscV.Ty.llvm i64)
    return %10 : (LLVMRiscV.Ty.llvm i64) → ()
}
