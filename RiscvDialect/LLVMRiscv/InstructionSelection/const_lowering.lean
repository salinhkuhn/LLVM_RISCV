import RiscvDialect.LLVMRiscv.LLVMAndRiscV
import RiscvDialect.LLVMRiscv.Refinement
import RiscvDialect.LLVMRiscv.Cast
import RiscvDialect.LLVMRiscv.forLeanMlir

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V

/- # lowering of constants   -/

/-- TO DO: lower multiple constants, because at the moment the frameowork
rewrites along the use-def chain and does not match on immediate values,
hence in our prototype we need to lower common constants explicitly.

to do: find out which are the most commonly used constants in code.  -/
def li_riscv_0 := [LV| {
    ^entry ():
      %0 = li (0)  : !i64
      %1 = "builtin.unrealized_conversion_cast" (%0) : (!i64) -> (i64)
      llvm.return %1 : i64
  }]
def const_llvm_0 : Com  LLVMPlusRiscV [] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry ():
      %1 = llvm.mlir.constant (0) : i64
      llvm.return %1 : i64
  }]
def llvm_const_lower_riscv_li_0 : LLVMPeepholeRewriteRefine [] :=
  {lhs:= const_llvm_0 , rhs:= li_riscv_0 ,
   correct := by
    unfold const_llvm_0 li_riscv_0
    simp_peephole
    simp [builtin.unrealized_conversion_cast.riscvToLLVM,  builtin.unrealized_conversion_cast.LLVMToriscv, LLVM.const?]
  }

def li_riscv_1 := [LV| {
    ^entry ():
      %0 = li (1)  : !i64
      %1 = "builtin.unrealized_conversion_cast" (%0) : (!i64) -> (i64)
      llvm.return %1 : i64
  }]
def const_llvm_1 : Com  LLVMPlusRiscV [] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry ():
      %1 = llvm.mlir.constant (1) : i64
      llvm.return %1 : i64
  }]
def llvm_const_lower_riscv_li_1 : LLVMPeepholeRewriteRefine [] :=
  {lhs:= const_llvm_1 , rhs:= li_riscv_1 ,
   correct := by
    unfold const_llvm_1 li_riscv_1
    simp_peephole
    simp [builtin.unrealized_conversion_cast.riscvToLLVM,  builtin.unrealized_conversion_cast.LLVMToriscv, LLVM.const?]
  }

def li_riscv_2 := [LV| {
    ^entry ():
      %0 = li (2)  : !i64
      %1 = "builtin.unrealized_conversion_cast" (%0) : (!i64) -> (i64)
      llvm.return %1 : i64
  }]
def const_llvm_2 : Com  LLVMPlusRiscV [] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry ():
      %1 = llvm.mlir.constant (2) : i64
      llvm.return %1 : i64
  }]
def llvm_const_lower_riscv_li_2 : LLVMPeepholeRewriteRefine [] :=
  {lhs:= const_llvm_2 , rhs:= li_riscv_2 ,
   correct := by
    unfold const_llvm_2 li_riscv_2
    simp_peephole
    simp [builtin.unrealized_conversion_cast.riscvToLLVM,  builtin.unrealized_conversion_cast.LLVMToriscv, LLVM.const?]
  }

def li_riscv_neg1 := [LV| {
    ^entry ():
      %0 = li (-1)  : !i64
      %1 = "builtin.unrealized_conversion_cast" (%0) : (!i64) -> (i64)
      llvm.return %1 : i64
  }]
def const_llvm_neg1 : Com  LLVMPlusRiscV [] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry ():
      %1 = llvm.mlir.constant (-1) : i64
      llvm.return %1 : i64
  }]
def llvm_const_lower_riscv_li_neg1 : LLVMPeepholeRewriteRefine [] :=
  {lhs:= const_llvm_neg1 , rhs:= li_riscv_neg1 ,
   correct := by
    unfold const_llvm_neg1 li_riscv_neg1
    simp_peephole
    simp [builtin.unrealized_conversion_cast.riscvToLLVM,  builtin.unrealized_conversion_cast.LLVMToriscv, LLVM.const?]
  }
