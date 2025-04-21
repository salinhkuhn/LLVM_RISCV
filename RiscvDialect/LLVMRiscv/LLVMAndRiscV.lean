import SSA.Core.MLIRSyntax.EDSL
import SSA.Core.Framework
import SSA.Core.Util
import SSA.Core.Util.ConcreteOrMVar
import SSA.Projects.InstCombine.ForStd
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.Tactic
import RiscvDialect.RISCV64.all

namespace LLVMRiscV
/- The types of this dialect contain the types modelled in the LLVM dialect
and in the Riscv Dialect. -/

inductive Ty where
  | llvm : InstCombine.Ty -> Ty
  | riscv :  RISCV64.Ty -> Ty


inductive Op where
  | llvm : InstCombine.Op -> Op
  | riscv : RISCV64.Op -> Op

@[simp]
abbrev LLVMPlusRiscV : Dialect where
  Op := Op
  Ty := Ty

/-
Types of this dialect are wrappers around the original LLVM / RISCV64 dialects.
Depending on the wrapper which signifies from which dialect the operation steems,
we dispatch the corresponding instance originating from the "source" dialect.
-/

instance : TyDenote (LLVMPlusRiscV.Ty) where
  toType := fun
    | .llvm llvmTy => TyDenote.toType llvmTy
    | .riscv riscvTy => TyDenote.toType riscvTy

@[simp, reducible]
def Op.sig : Op → List Ty
  | .llvm llvmop  => List.map Ty.llvm llvmop.sig
  | .riscv riscvop => List.map Ty.riscv riscvop.sig

@[simp, reducible]
def Op.outTy : Op → Ty
  | .llvm op => Ty.llvm (op.outTy)
  | .riscv op => Ty.riscv (op.outTy)

@[simp, reducible]
def Op.signature : Op → Signature (Ty) :=
  fun o => {sig := Op.sig o, outTy := Op.outTy o, regSig := []}

instance : DialectSignature LLVMPlusRiscV := ⟨Op.signature⟩


#check DialectDenote.denote
@[simp, reducible]
instance : DialectDenote (LLVMPlusRiscV) where
  denote
  | .riscv (riscvOp), args , x  => DialectDenote.denote riscvOp args x
  | .llvm (llvmOp), args , x  => DialectDenote.denote llvmOp args x

 /- | .riscv (riscvOp),_,_  =>
    match riscvOp with
    |.const val  => BitVec.ofInt 64 val -- const test case to figure out design
    | _ => BitVec.ofInt 64 0
  | .llvm llvmOp,_,_  =>
     match llvmOp  with
    |.const width val => some (BitVec.ofInt width val) -- const test case -/


def mkExpr (Γ : Ctxt _) (opStx : MLIR.AST.Op 0) :
  MLIR.AST.ReaderM (LLVMPlusRiscV) (Σ eff ty, Expr (LLVMPlusRiscV) Γ eff ty) := do
  -- RiscvMkExpr.mkExpr Γ opStx -- get type errors regarding the type of context Γ




end LLVMRiscV
-- etc for the other instances, each time just pattern-matching on whether the op/ty came from LLVM or RiscV, and dispatching to the relevant instance
