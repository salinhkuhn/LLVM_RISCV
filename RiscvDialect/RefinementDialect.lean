import RiscvDialect.RDialect
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.LLVM.PrettyEDSL
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForLean
import Lean

open toRISCV -- the riscv dialect
open InstCombine (LLVM)


/-
A context refinement is a function that maps each valid RISC-V variable (a de Bruijn index in Δ with type .bv)
 to a corresponding LLVM variable (a de Bruijn index in Γ with type .bitvec 64).
-/


def CtxtRefines (Γ : Ctxt LLVM.Ty) (Δ : Ctxt RV64.Ty) : Type := -- defining how to the types are mapped between the two contexts
  (Δ.Var .bv) → Γ.Var (.bitvec 64)

#print CtxtRefines

--def V₁:= (Ctxt.Valuation.ofHVector lh_llvm)
--def V₂:= (Ctxt.Valuation.ofHVector lh_riscv)
def LLVMCtxt := Ctxt InstCombine.Ty
def RISCVCtxt := Ctxt toRISCV.Ty



--def V₁:= (Ctxt.Valuation.ofHVector lh_llvm)
--def V₂:= (Ctxt.Valuation.ofHVector lh_riscv)

def toLLVM : RV64.Ty → InstCombine.Ty
  | .bv => .bitvec 64 -- keep in mind the InstCombine Ty is an otion bit vec

-- this defines how given a riscv context, the corresponding LLVM context should look under equailty assumptions
def RISCV_to_LLVM_should (B : Ctxt RV64.Ty) : (Ctxt LLVM.Ty) :=
  Ctxt.map toLLVM B

-- this checks that the LLVM context is exactly what the RISCV context would expect
def contextCrossDialectEquality1 (A : Ctxt InstCombine.Ty) (B : Ctxt RV64.Ty) : Prop :=
  (RISCV_to_LLVM_should B) = A


-- not sure how to implement this
def CtxtRefinesFunc (Γ : Ctxt LLVM.Ty) (Δ : Ctxt RV64.Ty) : Type := -- defining how to the types are mapped between the two contexts
  (Δ.Var .bv) → Γ.Var (.bitvec 64) -- from bit vec to option bit vec


structure ValutationRefinesEq {A : Ctxt InstCombine.Ty} {B: Ctxt RV64.Ty} (AV : A.Valuation) (BV : B.Valuation) where
  f : CtxtRefinesFunc A B
  val_refines : ∀ (v : B.Var .bv) (x : BitVec 64) , AV (f v) = some x → BV v = x

structure ValuationRefines {Γ : LLVMCtxt} {Δ : RISCVCtxt} (V₁ : Γ.Valuation) (V₂ : Δ.Valuation) where
  ctxtRefines : CtxtRefines Γ Δ -- defining how to values should be mapped, challenge; llvm type is option bc of UB
  val_refines : ∀ (v : Δ.Var .bv) (x : BitVec 64), V₁ (ctxtRefines v) = some x → V₂ v = x --if the llvm variable has a some value we have the riscv value given




-- my proposal but not sure of the context refinement
def CtxtRefinesFuncRiscvToLLVM (Γ : Ctxt LLVM.Ty) (Δ : Ctxt RV64.Ty) : Type := -- defining how to the types are mapped between the two contexts
 Γ.Var (.bitvec 64) → (Δ.Var .bv)
-- here then distingguish whether it is a none or some

structure ValuationProposal {Γ : LLVMCtxt} {Δ : RISCVCtxt} (V₁ : Γ.Valuation) (V₂ : Δ.Valuation) where
f : CtxtRefinesFuncRiscvToLLVM A B
val_refines : ∀ (v : Γ.Var (.bitvec 64)) (x : BitVec 64), V₁ v = some x → V₂ (f v) = x
-- if the llvm type is a some then there must be a corresponding value given by the ctxt mapping function
-- bc here as a next step in the proof i would need to extract what llvm variables where used and
-- bc the computation returns some would need have the implication that there must be a corresnding reiscv mapping

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

theorem see_LLVM2 (V₁) (V₂) (h : ValuationProposal V₁ V₂) :
    ∃ x, llvm_add.denote V₁ = some x → riscv_add.denote V₂ = x := by
    let ⟨ctxtRefines, val_refines⟩ := h
    simp_alive_meta
    cases h1 :  (llvm_add.denote V₁) with
    | none => use 42
              intro forContradiction
              contradiction
    | some val => use val
                  intro h'
                  injection h' with h''
                  rw [←h'']
                  simp [HVector.get, HVector.cons_get_zero]
                  simp_peephole
                  --unfold llvm_add at h1
                  --unfold riscv_add
                  -- i dont know how extract the variables now , I know I can use the refinement assumptions
                  -- i now want to extract the functions in
                  -- given the result of llvm_add I know the variable used from the LLVM side must have been some x
                  -- i also know the correspoding
                  unfold llvm_add at h1
                  sorry



theorem see_LLVM1 (V₁) (V₂) (h : ValuationRefines V₁ V₂) :
    ∃ x, llvm_add.denote V₁ = some x → riscv_add.denote V₂ = x := by
    let ⟨ctxtRefines, val_refines⟩ := h
    simp_alive_meta
    cases h1 :  (llvm_add.denote V₁) with
    | none => use 42
              intro forContradiction
              contradiction
    | some val => use val
                  intro h'
                  injection h' with h''
                  rw [←h'']
                  simp [HVector.get, HVector.cons_get_zero]
                  simp_peephole
                  --unfold llvm_add at h1
                  --unfold riscv_add
                  -- i dont know how extract the variables now , I know I can use the refinement assumptions
                  -- i now want to extract the functions in
                  -- given the result of llvm_add I know the variable used from the LLVM side must have been some x
                  -- i also know the correspoding
                  sorry

/-
have h1 : V₁ (ctxtRefines u₁) = some x₁ := ‹from earlier match›
have h2 : V₁ (ctxtRefines u₂) = some x₂ := ‹from earlier match›
have := val_refines u₁ x₁ h1
have := val_refines u₂ x₂ h2



-/



























      --let riscv_context := ctxtRefines (Ctxt.Var .bv 0)
      sorry




    sorry












#check llvm_add --(Γv : ((Ctxt.snoc [] toRISCV.Ty.bv).snoc toRISCV.Ty.bv).Valuation)
def lh_llvm : (HVector TyDenote.toType [InstCombine.Ty.bitvec 64,InstCombine.Ty.bitvec 64]) :=
          HVector.cons (some (BitVec.ofNat 64 20)) <| HVector.cons (some (BitVec.ofNat 64 2)) .nil
-- creating an HVector but specifying the types bc Lean can't just infer it


theorem see_LLVM_concrete3 V₁ V₂ (h : ValuationRefines V₁ V₂) : -- have the assumptions given by Valuation Refines
    (llvm_add.denote V₁ = some x )→ riscv_add.denote V₂ = x := by
      let ⟨ctxtRefines, val_refines⟩ := h
      simp_alive_meta
      intro lhs
      --split at h

















#check lh_llvm
#check lh_riscv
#check CtxtRefines
#check Ctxt toRISCV.Ty


theorem see_LLVM_concrete V₁ V₂ (h : ValuationRefines V₁ V₂) :
    eg21_b.denote V₁ = some x → eg22 V₂ = x := by
  unfold eg21_b eg22
  let ⟨ctxtRef, val_ref⟩ := h
  simp_alive_meta
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.add]
  unfold RV64.RTYPE_pure64_RISCV_ADD
  simp [HVector.cons_get_zero]
  simp_alive_undef
