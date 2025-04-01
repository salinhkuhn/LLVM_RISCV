import SSA.CORE.MLIRSyntax.EDSL
import SSA.Core.Framework
import SSA.Core.Util
import SSA.Core.Util.ConcreteOrMVar
import SSA.Projects.InstCombine.ForStd
import SSA.Projects.InstCombine.LLVM.Semantics
-- elaborate into Com and Exer

namespace RLLVMSemantics

def riscv.add_RTYPE (rs2_val : BitVec 64) (rs1_val : BitVec 64) :BitVec 64 :=
      BitVec.add rs1_val rs2_val


end RLLVMSemantics



namespace RLLVMDialect

section Dialect

open LLVM

inductive Op -- operations and information encoded into their opcode
| riscv.add
| llvm.add -- left out the flags for the moment
deriving Inhabited, DecidableEq, Repr


inductive Ty
| bitvector : Ty -- for LLVM ( or potentially I encode both as Some x )
| bv : Ty -- for RISCV
deriving Inhabited, DecidableEq, Repr

open TyDenote (toType) in

instance RLLVMTyDenote : TyDenote Ty where
toType --:= fun
|Ty.bv =>(BitVec 64)
|Ty.bitvector => Option (BitVec 64)

abbrev RLLVM : Dialect where
  Op := Op
  Ty := Ty

@[simp, reducible]
def Op.sig : Op -> List Ty
|.riscv.add => [Ty.bv, Ty.bv]
|.llvm.add  => [Ty.bitvector, Ty.bitvector]

def Op.outTy : Op -> Ty
|.riscv.add => Ty.bv
|.llvm.add  => Ty.bitvector


instance : DialectSignature RLLVM where
  signature op := ⟨op.sig, [], op.outTy, .pure⟩


-- denotation of each instr
def Op.denote (o : RLLVM.Op ) (op : HVector TyDenote.toType (DialectSignature.sig o)) :
  (RLLVMTyDenote.toType <| DialectSignature.outTy o) :=
match o with
| Op.llvm.add   => LLVM.add (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature]))      --(op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flags
| Op.riscv.add => RLLVMSemantics.riscv.add_RTYPE (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature]))

instance : DialectDenote RLLVM := ⟨
  fun o args _ => Op.denote o args -- from operation args return_value to calling the function behind the denotation
⟩

def mkTy : MLIR.AST.MLIRType φ → MLIR.AST.ExceptM RV64 RV64.Ty
  | MLIR.AST.MLIRType.undefined s => do
    match s with
    | "r64" => return .bv -- for the riscv dialect 
    | _ => throw .unsupportedType
  | _ => throw .unsupportedType

end Dialect

end RLLVMDialect


-- trying to do some add rewrite inside the new huge dialect
