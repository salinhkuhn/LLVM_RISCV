import SSA.Core.MLIRSyntax.EDSL
import SSA.Core.Framework
import SSA.Core.Util
import SSA.Core.Util.ConcreteOrMVar
import SSA.Projects.InstCombine.ForStd
import SSA.Projects.InstCombine.LLVM.Semantics
open LLVM

/-- this file is stil in progress and tried to modell riscv and llvm within one context.
Didnt continue implementing this so far.-/

namespace riscv.semantics


def RTYPE_pure64_RISCV_ADD (rs2_val : BitVec 64) (rs1_val : BitVec 64) :BitVec 64 :=
      BitVec.add rs1_val rs2_val

-- insert the llvm add semantics

end riscv.semantics

namespace llvm.semantics

end llvm.semantics

namespace llvm.riscv
section Dialect

inductive Op
|riscv.add
|llvm.add (nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
deriving DecidableEq, Repr


inductive Ty -- here belongs what my operations operate on
  | bv64 : Ty
  | opt64 : Ty
  -- need to add the llvm option type
  deriving DecidableEq, Repr

open TyDenote (toType) in
instance LLVMRISCVTyDenote : TyDenote Ty where
toType := fun
| Ty.bv64 => BitVec 64
| Ty.opt64 => Option (BitVec 64)

abbrev llvm.riscv : Dialect where
  Op := Op -- define the avaiable operations
  Ty := Ty -- define the avaiable types

@[simp, reducible]
def Op.sig : Op → List Ty
|riscv.add => [Ty.bv64, Ty.bv64]
|llvm.add _ => [Ty.opt64, Ty.opt64]
--|llvm.add =>


@[simp, reducible] -- reduceable means this expression can always be expanded by the type checker when type checking
def Op.outTy : Op  → Ty
|riscv.add => Ty.bv64
|llvm.add _ => Ty.opt64

@[simp, reducible]
def Op.signature : Op → Signature (Ty) :=
  fun o => {sig := Op.sig o, outTy := Op.outTy o, regSig := []}

instance : DialectSignature llvm.riscv := ⟨Op.signature⟩

@[simp, reducible]
instance : DialectDenote (llvm.riscv) where denote
  |.riscv.add, regs, _ => riscv.semantics.RTYPE_pure64_RISCV_ADD (regs.getN 0 (by simp [DialectSignature.sig, signature]))  (regs.getN 1 (by simp [DialectSignature.sig, signature]))
  |.llvm.add flags, regs, _  =>  LLVM.add (regs.getN 0 (by simp [DialectSignature.sig, signature])) (regs.getN 1 (by simp [DialectSignature.sig, signature])) flags
end Dialect

def riscv.add {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bv64) : Expr llvm.riscv Γ .pure .bv64  :=
  Expr.mk
    (op := llvm.riscv.Op.riscv.add)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def llvm.add {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .opt64) : Expr llvm.riscv Γ .pure .opt64  :=
  Expr.mk
    (op := llvm.riscv.Op.llvm.add)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def mkTy : MLIR.AST.MLIRType φ → MLIR.AST.ExceptM llvm.riscv llvm.riscv.Ty
  | MLIR.AST.MLIRType.undefined s => do
    match s with
    | "r64" => return .bv64 --maybe change it later
    | "i64" => return .opt64
    | _ => throw .unsupportedType
  | _ => throw .unsupportedType

instance instTransformTy : MLIR.AST.TransformTy llvm.riscv 0 where
  mkTy := mkTy


def mkExpr (Γ : Ctxt _) (opStx : MLIR.AST.Op 0) :
  MLIR.AST.ReaderM (llvm.riscv) (Σ eff ty, Expr (llvm.riscv) Γ eff ty) := do
    match opStx.args with
    | v₁Stx::v₂Stx:: [] =>
        let ⟨ty₁, v₁⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₁Stx
        let ⟨ty₂, v₂⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₂Stx
        match ty₁, ty₂, opStx.name with
        | .bv64 , .bv64 , "add" => --refers to an assembly add
              return ⟨ .pure, .bv64 ,⟨ .riscv.add, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .opt64 , .opt64 , "llvm.add" => -- unsure if handeld flags correctly
              return ⟨ .pure, .opt64 ,⟨ .llvm.add , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | _ ,_, _ => throw <| .unsupportedOp s!"wrong number of arguemnts, more than 2 arguemnts  {repr opStx}"
    | _  => throw <| .unsupportedOp "didnt implement instruction yet "

instance : MLIR.AST.TransformExpr (llvm.riscv) 0 where
  mkExpr := mkExpr

def mkReturn (Γ : Ctxt _) (opStx : MLIR.AST.Op 0) : MLIR.AST.ReaderM (llvm.riscv)
    (Σ eff ty, Com llvm.riscv Γ eff ty) :=
  if opStx.name == "return"
  then match opStx.args with
  | vStx::[] => do
    let ⟨ty, v⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ vStx
    return ⟨.pure, ty, Com.ret v⟩
  | _ => throw <| .generic s!"Ill-formed return statement (wrong arity, expected 1, got {opStx.args.length})"
  else throw <| .generic s!"Tried to build return out of non-return statement {opStx.name}"

instance : MLIR.AST.TransformReturn (llvm.riscv) 0 where
  mkReturn := mkReturn

open Qq MLIR AST Lean Elab Term Meta in
elab "[_| " reg:mlir_region "]" : term => do
  SSA.elabIntoCom reg q(llvm.riscv)

end llvm.riscv


open llvm.semantics
open llvm.riscv


def exampleLLVM : Com llvm.riscv [.opt64] .pure .opt64 :=
[_|{
  ^entry (%0: !i64 ):
  %1 = "llvm.add" (%0, %0) : (!i64, !i64 ) -> (!i64)
  "return" (%1) : ( !i64) -> ()
}]

-- why doesnt it work over a generic list
def exampleLLVMg {Γ : List llvm.riscv.Ty } : Com llvm.riscv Γ .pure .opt64 :=
[_|{
  ^entry (%0: !i64 ):
  %1 = "llvm.add" (%0, %0) : (!i64, !i64 ) -> (!i64)
  "return" (%1) : ( !i64) -> ()
}]


def exampleRiscv : Com llvm.riscv [.bv64] .pure .bv64 :=
[_| {
  ^entry (%0: !r64 ):
  %1 = "add" (%0, %0) : (!r64, !r64 ) -> (!r64)
  "return" (%1) : ( !r64) -> ()
}]

-- try to modell it as a rewrite but then have the problem of the denotation





-- do I need to establish a context mapping or exetend the context Γ
def instruction (e : Expr llvm.riscv Γ .pure .opt64) :  Expr llvm.riscv Γ .pure .bv64 :=
  match e with
  | Expr.mk
    (.llvm.add)
    (_)
    (_)
    (.cons e₁ <| .cons e₂ <| .nil ) -- are of type .opt64 which are option bitvector -> can either extract them and add them to the context but then need to know
    (_) =>  Expr.mk
    (op := .riscv.add)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ <| .nil  )
    (regArgs := .nil)
  | e  => e -- still wrong type

-- approach:
  -- lower it via transforming the expressions
  -- lower it via modelling the translation as rewrites


-- either let them be in the same context and add the riscv version of the varible to the context but then there is the issue of
-- how do I know which value it has (aka the llvm context would then get eleminated i guess)
def lowering {Γ Δ : Ctxt Ty} (com : Com llvm.riscv Γ .pure .opt64)(fuel : Nat) :  Com llvm.riscv Δ .pure .bv64  :=
  match com with
  | Com.ret x  =>  Com.ret x -- do I now need to know the valuation ? -- extract the variable and add it to the riscv context and then return that
  | Com.var (e) c' =>
  let e' := (instruction e)
  Com.var (e') (lowering c' (fuel - 1))
