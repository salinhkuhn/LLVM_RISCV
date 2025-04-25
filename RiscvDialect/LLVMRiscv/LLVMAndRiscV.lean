import SSA.Core.MLIRSyntax.EDSL
import SSA.Core.Framework
import SSA.Core.Util
import SSA.Core.Util.ConcreteOrMVar
import SSA.Projects.InstCombine.ForStd
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.Tactic
import RiscvDialect.RISCV64.all
set_option pp.fieldNotation false
open InstCombine(LLVM)
namespace LLVMRiscV
/- The types of this dialect contain the types modelled in the LLVM dialect
and in the Riscv Dialect. -/

private inductive Ty where
  | llvm : (Dialect.Ty LLVM) -> Ty
  | riscv : (Dialect.Ty RISCV64.RV64) -> Ty

private inductive Op where
  | llvm : (Dialect.Op LLVM) -> Op
  | riscv : (Dialect.Op RISCV64.RV64) -> Op
  | builtin.unrealized_conversion_cast.riscvToLLVM : Op
  | builtin.unrealized_conversion_cast.LLVMToriscv : Op

def builtin.unrealized_conversion_cast.riscvToLLVM (toCast : BitVec 64 ): Option (BitVec 64 ) := some toCast
/--
Casting a some x to x. The none (poison case) will be harded coded to zero bit vector as any
values refines a poison value.
-/
def builtin.unrealized_conversion_cast.LLVMToriscv (toCast : Option (BitVec 64)) : BitVec 64 := toCast.getD 0#64 -- rethink choice later


@[simp]
abbrev LLVMPlusRiscV : Dialect where
  Op := Op
  Ty := Ty

namespace LLVMPlusRiscV.Op

-- def llvm (llvmOp : LLVM.Op) : LLVMPlusRiscV.Op :=
--   --((@id (Dialect.Op LLVMPlusRiscV) <|
--     LLVMRiscV.Op.llvm llvmOp
--     --))


end LLVMPlusRiscV.Op

instance : TyDenote (Dialect.Ty LLVMPlusRiscV) where
  toType := fun
    | .llvm llvmTy => TyDenote.toType llvmTy
    | .riscv riscvTy => TyDenote.toType riscvTy

@[simp]
instance LLVMPlusRiscVSignature : DialectSignature LLVMPlusRiscV where
  signature
  | .llvm llvmOp => .llvm <$> DialectSignature.signature llvmOp
  | .riscv riscvOp => .riscv <$> DialectSignature.signature riscvOp
  | .builtin.unrealized_conversion_cast.riscvToLLVM => {sig := [Ty.riscv .bv], outTy := Ty.llvm (.bitvec 64), regSig := []}
  | .builtin.unrealized_conversion_cast.LLVMToriscv => {sig := [Ty.llvm (.bitvec 64)], outTy := (Ty.riscv .bv), regSig := []}
/-
@[simp, reducible]
def Op.sig : Op → List Ty
  | .llvm llvmop  => List.map Ty.llvm llvmop.sig

@[simp, reducible]
def Op.outTy : Op → Ty
  | .llvm op => Ty.llvm (op.outTy) -- dont understand why op is of type instCombine and not LLVM



@[simp, reducible]
def Op.signature : Op → Signature (Ty) :=
  fun o => {sig := Op.sig o, outTy := Op.outTy o, regSig := []}

instance : DialectSignature LLVMPlusRiscV := ⟨Op.signature⟩
-/

def extractllvmArgs : LLVMRiscV.Op → LLVM.Op
  | .llvm llvmOp => llvmOp
  | _ => .const 64 0 -- fallback case if function gets called on RISCV ops.


def extractriscvArgs : LLVMRiscV.Op → RISCV64.RV64.Op
  | .riscv riscvOp => riscvOp
  | _ => .const 0 -- fallback case if function gets called on LLVM ops.



#check LLVMRiscV.Op.llvm _
#check LLVMPlusRiscV.Op
-- #check (LLVMPlusRiscV.Op).llvm
-- #check (LLVMPlusRiscV.Op.llvm _  )

#check ((@id (Dialect.Op LLVMPlusRiscV) <| LLVMRiscV.Op.llvm _))
#check (Dialect.Op LLVMPlusRiscV)

example (d : Dialect) : d.Ty := by
  sorry


-- HVector toType (argumentTypes (.llvm llvmOp))
-- HVector toType ((argumentTypes llvmOp).map .llvm : List Hybrid.Ty)

-- args : HVector toType (argumentTypes llvmOp : List LLVM.Ty)
-- args[i] : toType (argumentTypes ...)[i]

-- #check LLVMPlusRiscV.Op.llvm
def llvmArgsFromHybrid : {tys : List LLVM.Ty} → HVector TyDenote.toType (tys.map LLVMRiscV.Ty.llvm) → HVector TyDenote.toType tys
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons x (llvmArgsFromHybrid xs)

 /-
 typeclass instance problem is stuck, it is often due to metavariable
  DialectSignature ?m.791
 -/
  -- HVector.map' (fun ty => (_ : LLVM.Op)) _ args

def riscvArgsFromHybrid : {tys : List RISCV64.RV64.Ty} → HVector TyDenote.toType (tys.map LLVMRiscV.Ty.riscv) → HVector TyDenote.toType tys
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons x (riscvArgsFromHybrid xs)

@[simp, reducible]
instance : DialectDenote (LLVMPlusRiscV) where
  denote
  | .llvm (llvmOp), args , .nil  => DialectDenote.denote llvmOp (llvmArgsFromHybrid args) .nil
  | .riscv (riscvOp), args , .nil  => DialectDenote.denote riscvOp (riscvArgsFromHybrid args) .nil
  | .builtin.unrealized_conversion_cast.riscvToLLVM, elemToCast, _  => builtin.unrealized_conversion_cast.riscvToLLVM (elemToCast.getN 0 (by simp [DialectSignature.sig, signature]))
  | .builtin.unrealized_conversion_cast.LLVMToriscv, elemToCast, _  => builtin.unrealized_conversion_cast.LLVMToriscv (elemToCast.getN 0 (by simp [DialectSignature.sig, signature]))

def ctxtTransformToLLVM  (Γ : Ctxt LLVMPlusRiscV.Ty) :=
  Ctxt.map  (fun ty  =>
    match ty with
    | .llvm someLLVMTy => someLLVMTy
    | .riscv _  => .bitvec 999
  ) Γ

#check Ctxt

#check Ctxt.Hom


-- def Ctxt.filterMap.aux (Γ : Ctxt Ty) (f : Ty → Option Ty') (iΓ : Nat) : Σ (Δ : Ctxt Ty'), Fin   :=
--   match Γ with
--   | [] => []
--   | t :: ts =>
--     match f t with
--     | .none => Ctxt.filterMap.aux ts f
--     | .some t' => t' :: Ctxt.filterMap.aux ts f

-- def ctxtTransformToLLVM? (Γ : Ctxt LLVMPlusRiscV.Ty) : Ctxt LLVM.Ty :=
--   Ctxt.filterMap.aux Γ (fun ty =>
--     match ty with
--     | .llvm ty => some ty
--     | _ => none
--   )

def ctxtTransformToRiscV (Γ : Ctxt LLVMPlusRiscV.Ty) :=
  Ctxt.map  (fun ty  =>
    match ty with
    | .riscv someRiscVTy  => someRiscVTy
    | _  => .bv -- unsure what to return here because want to signal in case transformation is not valid
  ) Γ

/-- Projection of `outTy` commutes with `Signature.map`. -/
@[simp]
theorem outTy_map_signature_eq {s : Signature α} {f : α → β} :
  Signature.outTy (f <$> s) = f s.outTy := rfl

-- @bollu says @salinhkuhn should work directly on lean-mlir, rather than using as a submodule,
-- because the development is complex enough to constantly add new features into lena-mlir
def _root_.HVector.foldlM {B : Type*} [Monad m] (f : ∀ (a : α), B → A a → m B) :
    ∀ {l : List α}, (init : B) → (as : HVector A l) → m B
  | [],   b, .nil       => return b
  | t::_, b, .cons a as => do foldlM f (← f t b a) as

/-- Simultaneous map on the type and value level of an HVector. -/
def _root_.HVector.ubermap {A : α → Type} {B : β → Type}
    {l : List α}
    (F : α → β)
    (f : {a : α} → (v : A a) → B (F a) )
    (as : HVector A l) : (HVector B (F <$> l)) :=
  match l, as with
  | [], .nil => .nil
  | _t :: _ts, .cons a as => HVector.cons (f a) (HVector.ubermap F f as)

/--
Simultaneous map on the type and value level of an HVector while performing monadic effects for value translation.
-/
def _root_.HVector.ubermapM [Monad m] {A : α → Type} {B : β → Type}
    {l : List α}
    {F : α → β}
    (f : (a : α) → (v : A a) → m (B (F a)) )
    (as : HVector A l) : m (HVector B (F <$> l)) :=
  match l, as with
  | [], .nil => return .nil
  | t :: _ts, .cons a as => do return HVector.cons (← f t a) (← HVector.ubermapM f as)

def transformExprLLVM (e : Expr (InstCombine.MetaLLVM 0) (ctxtTransformToLLVM Γ) eff ty) :
  MLIR.AST.ReaderM (LLVMPlusRiscV) (Expr LLVMPlusRiscV Γ eff (.llvm ty)) :=
    match e with
    | Expr.mk op1 ty_eq1 eff_le1 args1 regArgs1 => do
        -- args1 : HVector (Ctxt.Var (ctxtTransformToLLVM Γ)) (DialectSignature.sig op1)
        let args' : HVector (Ctxt.Var Γ) (.llvm <$> DialectSignature.sig op1) ←
          args1.ubermapM fun t v => do
            match h : Γ.get? v.val with
            | some ty' => do
              match hty : ty' with
              | .riscv _ =>
                throw <| .generic s!"INTERNAL ERROR: This case is impossible, LLVM expression is pointing to RISCV variable."
              | .llvm originalLLVMTy =>
                if hty' : originalLLVMTy = t then
                  return ⟨v.val, by rw [h, hty']⟩
                else
                  throw <|.generic s!"INTERNAL ERROR: This case is impossible, LLVM expression is pointing to an incorrect bitwidth LLVM argument."
                  -- return ⟨v.val, by rw [h]⟩
            | none =>
              -- this is impossible, because ctxtTransformToLLVM is a `List.map`, which always maintains length.
              -- sorry
              throw <| .generic s!"INTERNAL ERROR: This case is impossible, as 'ctxtTransformToLLVM' is length-preserving."
        return Expr.mk
          (op := Op.llvm op1)
          (eff_le := eff_le1)
          (ty_eq := ty_eq1 ▸ rfl) -- @bollu: Discussion with Alex needed about cute-ism.
          (args := args')-- .cons e₁ <| .cons e₂ .nil)
          (regArgs := HVector.nil)
        -- LLVMPlusRiscV Γ eff (.llvm ty)

-- def transformExprLLVMCasesArgs  (e : Expr (InstCombine.MetaLLVM 0) (ctxtTransformToLLVM Γ) eff ty) :=
--   match e with
--   | Expr.mk op1 ty_eq1 eff_le1 args regArgs1 =>
--       Expr.mk
--       (op := LLVMPlusRiscV.Op.llvm op1 )
--       (eff_le := eff_le1 )
--       (ty_eq := by rfl)
--       (args := _ )-- .cons e₁ <| .cons e₂ .nil)
--       (regArgs := HVector.nil)
--       -- LLVMPlusRiscV Γ eff (.llvm ty)
/-

def rem {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bv) : Expr RV64 Γ .pure .bv  :=
  Expr.mk
    (op := Op.rem)
    (eff_le := by constructor)
    (ty_eq := by rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

-/


#check Expr.mk
#check Ctxt.Var

-- def transformExprRiscV (e : Expr (InstCombine.MetaLLVM 0) (ctxtTransformToLLVM Γ) eff ty) :  Expr LLVMPlusRiscV Γ eff (LLVMRiscV.Ty.llvm ty)  :=
--   sorry

def mkExpr (Γ : Ctxt _) (opStx : MLIR.AST.Op 0) :
  MLIR.AST.ReaderM (LLVMPlusRiscV) (Σ eff ty, Expr (LLVMPlusRiscV) Γ eff ty) := do

  let llvmParse := InstcombineTransformDialect.mkExpr (ctxtTransformToLLVM  Γ) opStx (← read) -- reading state out of the monad.
  match llvmParse with
    | .ok ⟨eff, ty, expr⟩ => do -- returns llvm expression
      let v ← transformExprLLVM expr
      return ⟨eff, .llvm ty, v⟩

      -- return ⟨eff, (.llvm ty),  .llvm expr⟩
      -- llvmParse
       -- transform the expression back
    | .error (.unsupportedOp _) => do
     let ⟨eff, (ty) , expr⟩ ← RiscvMkExpr.mkExpr (ctxtTransformToRiscV Γ) opStx (← read)
      --let ⟨eff, ty, expr⟩ ← ...
      -- parse it as riscv
     -- transform the expression back into my context
      return _
    | .error e => throw <| .generic s!"Ill-formed program, coulnd't parse it as llvm nor riscv."



instance : MLIR.AST.TransformExpr (LLVMPlusRiscV) 0 where
  mkExpr := mkExpr

end LLVMRiscV
-- etc for the other instances, each time just pattern-matching on whether the op/ty came from LLVM or RiscV, and dispatching to the relevant instance
