import RiscvDialect.RDialect
import RiscvDialect.RefinementDialect
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.LLVM.PrettyEDSL
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForLean
import RiscvDialect.Instructions.riscv_instructions
import RiscvDialect.Instructions.llvm_instructions
import RiscvDialect.Peephole_Optimizations.RISCVRewrites
import Lean

open toRISCV
open RV64
open InstCombine (LLVM)

/-
this file contains the actually implementation of the instruction selection.
we transalte a Com in operating on context of type α and dialect D1 to a com operating on context of type β and dialect D2.
-/


def LLVMCtxtToRV (Γ : Ctxt LLVM.Ty) : Ctxt RV64.Ty :=
  List.replicate Γ.length (.bv)

/--TO DO: ask for a shorter proof.-/

def LLVMVarToRV : Γ.Var (.bitvec 64) → (LLVMCtxtToRV Γ).Var .bv
  | ⟨i, h⟩ =>  ⟨i, by
    simp [LLVMCtxtToRV]
    have hcontra2 : Γ.get? i = some (InstCombine.Ty.bitvec 64) := by exact h
    have hcontra3: List.length Γ ≤ i → Γ.get? i  = none := by simp [List.get?]
    have hcontra : i <  Γ.length :=  by
      by_contra h
      simp at h
      have h_none : Γ.get? i = none := hcontra3 h
      rw [hcontra2] at h_none
      contradiction
    have leng_eq_leng : i < List.length Γ → i < List.length (List.replicate (List.length Γ) Ty.bv) := by simp
    have h3 : i < (List.replicate (List.length Γ) Ty.bv).length := by exact leng_eq_leng hcontra
    have h4 : (List.replicate (List.length Γ) Ty.bv)[i] = Ty.bv → (List.replicate (List.length Γ) Ty.bv)[i]? = some Ty.bv := by
        simp [List.get?_eq_some]
        exact hcontra
    apply h4
    rfl
   ⟩



-- function that rewrites ahn expression into a computation
variable {d} [DialectSignature d]
def Com.ofExpr : Expr d Γ eff t → Com d Γ eff t := fun e =>
  Com.var e <| Com.ret <| Ctxt.Var.last _ _


-- LLVM INSTRUCTION MAPPING TO RISCV: ONE-TO-ONE
-- this works if these are single instruction level mappings
def transfToRISCVoneToOne  (e : Expr LLVM Γ .pure (.bitvec 64)) :  Expr RV64 (LLVMCtxtToRV Γ) .pure (.bv)  :=
match e with
  -- ADD (with or without overflow)
  | Expr.mk (InstCombine.Op.add 64 nswnuw') _ _ (e ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (toRISCV.Op.add) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- SUB
  | Expr.mk (InstCombine.Op.sub 64 nswnuw') _ _ (e ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (toRISCV.Op.sub) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil -- double check if order is correct
  -- AND
  |Expr.mk (InstCombine.Op.and 64) _ _ (e ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (toRISCV.Op.and) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- OR NOMRAL
  |Expr.mk (InstCombine.Op.or 64  ⟨false⟩) _ _ (e ::ₕ (e2 ::ₕ .nil)) _  => -- disjoint or aka "or":: double check the mapping
      Expr.mk (toRISCV.Op.or) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  --OR DISJOINT
  |Expr.mk (InstCombine.Op.or 64  ⟨true⟩) _ _ (e ::ₕ (e2 ::ₕ .nil)) _  => -- disjoint or aka "or":: double check the mapping:: to be specified what the disjoint or will in riscv
      Expr.mk (toRISCV.Op.or) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  --XOR
  |Expr.mk (InstCombine.Op.xor 64 ) _ _ (e ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (toRISCV.Op.xor) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  --MUL
  |Expr.mk (InstCombine.Op.mul 64 ⟨false, false⟩ ) _ _ (e ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (toRISCV.Op.mul) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  --UREM -- CHECK BECAUSE OF SIGNS
  |Expr.mk (InstCombine.Op.urem 64 ) _ _ (e ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (toRISCV.Op.remu) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  --ASHR -- to do check the flags and their implication
  |Expr.mk (InstCombine.Op.ashr 64 flags ) _ _ (e ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (toRISCV.Op.sra) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- SDIV -- check the under- and overflow
  |Expr.mk (InstCombine.Op.sdiv 64 flags ) _ _ (e ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (toRISCV.Op.div) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- UDIV
  |Expr.mk (InstCombine.Op.udiv 64 flags ) _ _ (e ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (toRISCV.Op.divu) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- FALLBACK FUNCTION
  |e => Expr.mk (toRISCV.Op.const 0) (eff_le := by constructor) (ty_eq := rfl) (.nil) (.nil)


/- -TO DO: implement prepending of one computation onto antoher computation
this function preprends a computation onto another computation => to do : think of how to do this -/
variable {d : Dialect} [DialectSignature d] in
def Com.prependCom (e : Com d Γ eff α) (body : Com d (Γ.snoc α) eff β) : Com d Γ eff β :=
  sorry


/--- LLVM INSTRUCTIONS THAT MAP TO MANY RISCV INSTRUCTION
-- the purpose of this function is account for one to many lowerings where to mapping is not trivial. -/
def transfToRISCVoneToMany  : (e : Expr LLVM Γ .pure (.bitvec 64)) →  Com RV64 (LLVMCtxtToRV Γ) .pure (.bv)
  -- neg = const 0 && sub
  | Expr.mk (InstCombine.Op.neg 64) _ _ ((e1 ::ₕ .nil)) _ =>
        let expr1 := Expr.mk (toRISCV.Op.const (0)) (eff_le := by constructor) (ty_eq := rfl) (.nil) (.nil);
        let expr2 := Expr.mk (toRISCV.Op.sub) (eff_le := by constructor) (ty_eq := rfl) ( (LLVMVarToRV (Ctxt.Var.last _ _)) ::ₕ ((LLVMVarToRV e1) ::ₕ .nil)) .nil
        --  Com.prependCom (Com.ofExpr expr1) (Com.ofExpr expr2)
        Com.var expr1 (Com.var (expr2)  (Com.ret (Ctxt.Var.last _ _)))
      -- goal of this is to get 0-x :: debug semantics of sub aka order of sub
  | e => Com.ofExpr (transfToRISCVoneToOne e) -- fall back case of when this function actually gets called with a expr that can be mapped one to one


-- TO DO: unsure if like this modelling as an option, makes things not that pretty.
-- THIS FUNCTION ONLY SUPPORTS ONE TO ONE LOWERINGS
-- if we return a none then we must have an invalid input or the computation must have failed,
def loweringLLVMtoRISCV : {Γ : Ctxt LLVM.Ty} → (com : Com LLVM Γ .pure (.bitvec 64)) → Option (Com RV64 (LLVMCtxtToRV Γ)  .pure (.bv))
  | _, Com.ret x  =>  some (Com.ret (LLVMVarToRV x))
  | _, Com.var (α := InstCombine.Ty.bitvec 64) e c' =>
        let e' := (transfToRISCVoneToOne e) -- map the expression to a riscv expression
        match loweringLLVMtoRISCV c' with
        | some com => some (Com.var (e') (com))
        | none => none
  | _, Com.var (α := InstCombine.Ty.bitvec _) _ _ =>
      none


def isOneToOne (expr : Expr LLVM Γ .pure (.bitvec 64)) :=
  match expr.op  with
  | InstCombine.Op.neg 64 => false
  |_ => true

/-
this function computes the LLVM to RISCV lowering, return some comp, where comp is the corresponding riscv lowering.
Returning none if the type of operation is not on a bitvec 64.
Which is not expected and supported as register and llvm ir operations are definedc on 64-bit vectors.
-/

-- this function supports onetoone and onetomany lowerings
def loweringLLVMtoRISCVextended : {Γ : Ctxt LLVM.Ty} → (com : Com LLVM Γ .pure (.bitvec 64)) → Option (Com RV64 (LLVMCtxtToRV Γ)  .pure (.bv))
  | _, Com.ret x  =>  some (Com.ret (LLVMVarToRV x))
  | _, Com.var (α := InstCombine.Ty.bitvec 64) e c' =>
        if (isOneToOne e) then
          let e' := (transfToRISCVoneToOne e) -- map the expression to a riscv expression
          match loweringLLVMtoRISCVextended c' with
          | some com => some (Com.var (e') (com))
          | none => none
        else -- the one to many case
          let comp :=  transfToRISCVoneToMany e -- the computation that is needed to represent the lowering of the llvm instruction
          match loweringLLVMtoRISCVextended c' with
          | some com => some (Com.prependCom comp com ) -- this  preprends the computation needed for the expression lowering to the rest of the computation.
          | none => none
  | _, Com.var (α := InstCombine.Ty.bitvec _) _ _ =>
      none

-- bellow are examples to check my lowerings
def llvm_sub1 :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.sub  %Y, %X : i64
      llvm.return %v1 : i64
  }]

def riscv_sub1 :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.sub" (%Y, %X ) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]

def riscv_add_add :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.add" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]

def llvm_add_add :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add  %X, %Y : i64
      llvm.return %v1 : i64
  }]

def riscv_add_sub :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.add" (%X, %Y) : (!i64, !i64) -> (!i64)
    %v2 = "RV64.sub" (%v1, %v1) : (!i64, !i64) -> (!i64)
    "return" (%v2) : (!i64, !i64) -> ()
  }]

def llvm_add_sub :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add  %X, %Y : i64
      %v2 = llvm.sub %v1, %v1 : i64
      llvm.return %v2 : i64
  }]

def llvm_const_add :=
    [llvm(64)| {
^bb0(%X : i64):
      %v1 = llvm.mlir.constant 0 :i64
      %v2 = llvm.add  %X, %v1 : i64
      llvm.return %v2 : i64
  }]

def llvm_neg :=
    [llvm(64)| {
      ^bb0(%X : i64):
      %v1 = llvm.neg %X :i64
      llvm.return %v1 : i64
  }]

def riscv_neg :=
  [RV64_com| {
    ^entry (%X: !i64):
    %v1 = "RV64.const" () { val = 0 : !i64 } : (!i64, !i64) -> (!i64)
    %v2 = "RV64.sub" (%v1, %X) : (!i64, !i64) -> (!i64)
    "return" (%v2) : (!i64, !i64) -> ()
  }]

def riscv_const_add :=
  [RV64_com| {
    ^entry (%X: !i64):
    %v1 = "RV64.const " () { val = 0 : !i64 } : (!i64, !i64) -> (!i64)
    %v2 = "RV64.add" (%X, %v1) : (!i64, !i64) -> (!i64)
    "return" (%v2) : (!i64, !i64) -> ()
  }]

-- TEST LOWERINGS FOR THE ONE TO ONE LOWERING
--def loweringLLVMNegAsExpected :  loweringLLVMtoRISCV (llvm_neg) = some (riscv_neg) := by native_decide :: not supported because requires many to many lowering
-- checking that the lowering yield code as expected
def loweringLLVMAddAsExpected : loweringLLVMtoRISCV llvm_add = some (riscv_add) := by native_decide
def loweringLLVMSubExpected : loweringLLVMtoRISCV llvm_sub1 = some (riscv_sub1) := by native_decide
def loweringLLVMDoubleAddAsExpected : loweringLLVMtoRISCV llvm_add_add = some (riscv_add_add) := by native_decide
def loweringLLVMAddSubAsExpected : loweringLLVMtoRISCV llvm_add_sub = some (riscv_add_sub) := by native_decide
def loweringConstAdd : loweringLLVMtoRISCV llvm_const_add = some (riscv_const_add) := by native_decide

def rhs_add0_com :  Com RV64 [.bv] .pure .bv := Com.ret ⟨0, by simp [Ctxt.snoc]⟩
#check rhs_add0_com



-- TEST LOWERINGS FOR THE ONE TO MANY LOWERING : CANT EVALUATE YET BECAUSE LEMMA NOT PROVEN AT THE MOMENT
def loweringLLVMNegAsExpected2 :  loweringLLVMtoRISCVextended (llvm_neg) = some (riscv_neg) := by native_decide
-- examples and checks wether this is lowering makes sense
def rhs_add0_com2 :  Com RV64 [.bv] .pure .bv := Com.ret ⟨0, by simp [Ctxt.snoc]⟩
#check rhs_add0_com
-- checking that the lowering yield code as expected
def loweringLLVMAddAsExpected2 : loweringLLVMtoRISCVextended llvm_add = some (riscv_add) := by native_decide
-- because sub lowering doesnt exist yet
def loweringLLVMSubExpected2 : loweringLLVMtoRISCVextended llvm_sub1 = some (riscv_sub1) := by native_decide
def loweringLLVMDoubleAddAsExpected2 : loweringLLVMtoRISCVextended llvm_add_add = some (riscv_add_add) := by native_decide
def loweringLLVMAddSubAsExpected2 : loweringLLVMtoRISCVextended llvm_add_sub = some (riscv_add_sub) := by native_decide
def loweringConstAdd2 : loweringLLVMtoRISCVextended llvm_const_add = some (riscv_const_add) := by native_decide

def rhs : Com RV64 [.bv] .pure .bv := Com.var (const 0) (
  Com.var (add ⟨1, by simp[Ctxt.snoc]⟩ ⟨0, by simp[Ctxt.snoc]⟩) -- x + 0
      (Com.ret ⟨2, by simp[Ctxt.snoc]⟩))


-- now just need to revert this and rewrite it into the IR again


--PLAYING AROUND WITH PEEPLHOLE OPTIMIZATIONS
-- couldnt figue out to appy the rewrites onto a some Computation yet.
def optimizedCode: Com RV64 [.bv] .pure .bv := rewritePeepholeAt rewrite_add0 1 riscv_const_add
-- now try run rewritting pass on the generated riscv-code
def applyPeepholeOptimizationOnRewritten : some (optimizedCode) = some rhs := by native_decide

/-
def loweringLLVMRet :  loweringLLVMtoRISCV llvm_ret = some (riscv_ret) := by native_decide
def loweringLLVMReturnAsExpected :
  some  ([RV64_com| {
    ^entry (%0 : !i64 ):
      "return" (%0) : ( !i64 ) -> ()
  }])
  =
  (loweringLLVMtoRISCV (
  [llvm(64)| {
    ^bb0(%X : i64):
    llvm.return %X : i64
  }])) := by native_decide
-/
