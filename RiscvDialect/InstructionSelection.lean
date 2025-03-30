import RiscvDialect.RDialect
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.LLVM.PrettyEDSL
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForLean
import Lean


-- this file contains everything I want rto proof but haven't managed yet and I need help in doing so !

def riscv_add :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.add" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]


def llvm_add :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add %Y, %X : i64
      llvm.return %v1 : i64
  }]

#check llvm_add --(Γv : ((Ctxt.snoc [] toRISCV.Ty.bv).snoc toRISCV.Ty.bv).Valuation)
def lh_llvm : (HVector TyDenote.toType [InstCombine.Ty.bitvec 64,InstCombine.Ty.bitvec 64]) :=
          HVector.cons (some (BitVec.ofNat 64 20)) <| HVector.cons (some (BitVec.ofNat 64 2)) .nil
-- creating an HVector but specifying the types bc Lean can't just infer it


def LLVMCtxt := Ctxt InstCombine.Ty
def RISCVCtxt := Ctxt toRISCV.Ty

def x := LLVMCtxt
#check LLVMCtxt


def CtxtRefines (Γ : LLVMCtxt) (Δ : RISCVCtxt) : Type := -- defining how to the types are mapped between the two contexts
  (Δ.Var .bv) → Γ.Var (.bitvec 64)

#print CtxtRefines

--def V₁:= (Ctxt.Valuation.ofHVector lh_llvm)
--def V₂:= (Ctxt.Valuation.ofHVector lh_riscv)
structure ValuationRefines {Γ : LLVMCtxt} {Δ : RISCVCtxt} (V₁ : Γ.Valuation) (V₂ : Δ.Valuation) where
  ctxtRefines : CtxtRefines Γ Δ -- defining how to values should be mapped, challenge; llvm type is option bc of UB
  val_refines : ∀ (v : Δ.Var .bv) (x : BitVec 64), V₁ (ctxtRefines v) = some x → V₂ v = x --if the llvm variable has a some value we have the riscv value given












def toLLVM : RV64.Ty → InstCombine.Ty
  | .bv => .bitvec 64 -- keep in mind the InstCombine Ty is an otion bit vec

-- this defines how given a riscv context, the corresponding LLVM context should look under equailty assumptions
def RISCV_to_LLVM_should (A : Ctxt LLVM.Ty) (B : Ctxt RV64.Ty) : (Ctxt LLVM.Ty) :=
  Ctxt.map toLLVM B

-- this checks that the LLVM context is exactly what the RISCV context would expect
def contextCrossDialectEquality1 (A : Ctxt LLVM.Ty) (B : Ctxt RV64.Ty) : Prop :=
  (RISCV_to_LLVM_should A B) = A

-- not sure how to implement this
def CtxtRefinesFunc (Γ : Ctxt LLVM.Ty) (Δ : Ctxt RV64.Ty) : Type := -- defining how to the types are mapped between the two contexts
  (Δ.Var .bv) → Γ.Var (.bitvec 64) -- from bit vec to option bit vec
  -- how to indices of bv variable map to bitvec 64 var

structure ValutationRefinesEq {A : Ctxt LLVM.Ty} {B: Ctxt RV64.Ty} (AV : A.Valuation) (BV : B.Valuation) where
  ctxtRefines : contextCrossDialectEquality1 A B
  f : CtxtRefinesFunc A B
  val_refines : ∀ (v : B.Var .bv) (x : BitVec 64) , AV (f v) = some x → BV v = x

-- could modell then then as instruction selection nodes that take in a context and process it
-- llvm ir program, split it up into instruction aka single function calls
-- then then try to proof using autmation and simp lemmas that i can seuqntially apply the translation lemmas
-- when each instruction is the same all the whoke smeanitxs is the same because it is ssa


theorem add_select (V₁) (V₂) (h : ValuationRefines V₁ V₂) :
  ∃ x,  ([llvm(64)| {
    ^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add %Y, %X : i64
      llvm.return %v1 : i64
  }].denote V₁ -- check that it is not poisson
  = some x)
  →
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.add" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }].denote V₂ = x := by sorry







-- framework to translate across dialects
theorem translate_add :
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add %Y, %X : i64
      llvm.return %v1 : i64
  }] ⊑
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.add" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }] := sorry












theorem see_LLVM_concrete3 LLVMVal RISCVVal (h : ValuationRefines LLVMVal RISCVVal) : -- have the assumptions given by Valuation Refines
    eg21_b.denote V₁ = some x → eg22 V₂ = x := by sorry  -- llvm to risc-v




theorem see_LLVM_concrete3 V₁ V₂ (h : ValuationRefines V₁ V₂) : -- have the assumptions given by Valuation Refines
    eg21_b.denote V₁ = some x → eg22 V₂ = x := by sorry  -- llvm to risc-v



#check CtxtRefines
#check Ctxt toRISCV.Ty

/-
theorem see_LLVM_concrete V₁ V₂ (h : ValuationRefines V₁ V₂) :
    eg21_b.denote V₁ = some x → eg22 V₂ = x := by
  unfold eg21_b eg22
  let ⟨ctxtRef, val_ref⟩ := h
  simp_alive_meta
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.add]
  unfold RV64.RTYPE_pure64_RISCV_ADD
  simp [HVector.cons_get_zero]
  simp_alive_undef

theorem see_LLVM (V₁) (V₂) (h : ValuationRefines V₁ V₂) :
  eg21_b.denote V₁ = some x → eg22 V₂ = x := by
  unfold eg21_b eg22
-/




theorem see_LLVM1 (V₁) (V₂) (h : ValuationRefines V₁ V₂) :
    ∃ x, eg21_b.denote V₁ = some x → eg22 V₂ = x := by
  unfold eg21 eg22
  sorry





  --simp only [Com.denote]
  simp_alive_meta
  simp_peephole
  --simp [DialectDenote.denote]
  let ⟨ctxtRef, val_ref⟩ := h
  let X_RV := Ctxt.Var.last [] toRISCV.Ty.bv
  let Y_RV := Ctxt.Var.last [toRISCV.Ty.bv] toRISCV.Ty.bv
  let X_LL := h.ctxtRefines X_RV
  let Y_LL := h.ctxtRefines Y_RV
  cases V₁ X_LL with --none or some
  | none  => sorry
  | some x₁ => -- resolving x first
    cases V₁ Y_LL with
      | none => sorry
      | some x₂ =>
