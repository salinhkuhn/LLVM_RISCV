import RiscvDialect.LLVMRiscv.PeepholeRewriteRefine

open llvm.riscv
open riscv.semantics
open LLVM
/-!
## Functionality
This file contains rewrites for the Peephole Rewriter to eliminate unrealized conversion cast.
The rewrites bellow are registered and similar to dead code elimination/ constant folding
unrealized conversion cast get eliminated.

An `unrealized conversion cast` in MLIR is an operation inserted during the lowering
from one dialect to another dialect to temporary guarantee compatible between type
systems. It is stating that an element should be casted to type B from type A.
The actual casting needs to be performed by a separate pass.
-/

/-
Rewrite to eliminate ` option bitvec ->  bitvec -> opt bitvec casts`.
The step `option bitvec -> bitvec ` requires a notion of refinement.
The current defintion can have some rethinking, but currently we define the refinement
of a `some x` to be `x` itself only, and `any value` refines `x`.
-/
def cast_cast_eq_cast_out_llvm : RiscVPeepholeRewriteRefine ([Ty.opt64]) :=
  {lhs:=
    [_| {
    ^entry (%0: !i64 ):
    "return" (%0) : (!i64) -> ()
  }], rhs:=
    [_| {
    ^entry (%0: !i64 ):
    %1 = "builtin.unrealized_conversion_cast.LLVMToriscv" (%0) : (!i64) -> (!r64)
    %2 = "builtin.unrealized_conversion_cast.riscvToLLVM" (%1) : (!r64) -> (!i64)
    "return" (%2) : (!i64) -> ()
  }] ,
   correct:=
    by
    simp_peephole
    intro e'
    simp [riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv, riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM]
    cases e'
    . simp only [Option.getD_none, BitVec.Refinement.none_left]
    . simp only [Option.getD_some, BitVec.Refinement.refl]
    }

/-
rewrite to eliminate `bitvec -> opt bitvec -> bitvec casts`.
-/
def cast_cast_eq_cast_out_riscv : PeepholeRewrite llvm.riscv ([Ty.bv64]) .bv64 :=
  {lhs:=
    [_| {
    ^entry (%0: !r64 ):
    "return" (%0) : (!r64) -> ()
  }], rhs:=
    [_| {
    ^entry (%0: !r64 ):
    %1 = "builtin.unrealized_conversion_cast.riscvToLLVM" (%0) : (!r64) -> (!i64)
    %2 = "builtin.unrealized_conversion_cast.LLVMToriscv" (%1) : (!i64) -> (!r64)
    "return" (%2) : (!r64) -> ()
  }] ,
   correct:=
    by
    simp_peephole
    intro e'
    simp [riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv, riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM]
    }
