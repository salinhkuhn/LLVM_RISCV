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


def allVarsRiscv (Δ : Ctxt (toRISCV.Ty)) : List (Δ.Var .bv) :=
  (List.range Δ.length).map (fun i =>
    ⟨i, sorry⟩)

def allVarsLLVM (Γ : Ctxt (InstCombine.Ty)) : List (Γ.Var (.bitvec 64)) :=
  (List.range Γ.length).map (fun i =>
    ⟨i, sorry⟩)

-- type of var is a DeBruijn index meaning a nat and a proof that the nat has the correspodning type
def evalContextRiscv (Δ : RISCVCtxt) (V₁ : Δ.Valuation) : List (BitVec 64) :=
  (allVarsRiscv Δ).map (@V₁ _)


-- type of var is a DeBruijn index meaning a nat and a proof that the nat has the correspodning type
def evalContextLLVM(Γ : Ctxt (InstCombine.Ty)) (V₁ : Γ.Valuation) : List (Option (BitVec 64)) :=
  (allVarsLLVM Γ).map (@V₁ _)

/-
List (BitVec 64)
-/

/-
structure ValuationRefines {Γ : LLVMCtxt} {Δ : RISCVCtxt} (V₁ : Γ.Valuation) (V₂ : Δ.Valuation) where
  ctxtRefines : CtxtRefines Γ Δ -- defining how to values should be mapped, challenge; llvm type is option bc of UB
  val_refines : ∀ (v : Δ.Var .bv) (x : BitVec 64), V₁ (ctxtRefines v) = some x → V₂ v = x
-/

def convertLLVMContextToRiscv (LLVMVariables : List (Option (BitVec 64))) : List ((BitVec 64)) :=
  LLVMVariables.foldr (fun x acc =>
    match x with
    | some v => v :: acc
    | none   => acc
  ) []

def dialectContextTransform2 (Δ : RISCVCtxt) (Γ : LLVMCtxt) (f :RV64.Ty → LLVM.Ty ): Prop :=
  (Ctxt.map f Δ) = Γ
/-
def dialectValuationTransform (Δ : RISCVCtxt) (Γ : LLVMCtxt) (f :RV64.Ty → LLVM.Ty ) : Prop :=
  (Ctxt.map f Δ) = Γ ∧ Ctxt.map (Ctxt.Valuation Δ RV64TyDenote.toType) Δ
-/

def dialectValuationTransform (Δ : RISCVCtxt) (Γ : LLVMCtxt) (V₁ : Γ.Valuation) (V₂ : Δ.Valuation): Prop :=
  convertLLVMContextToRiscv (evalContextLLVM Γ V₁)  = (evalContextRiscv Δ V₂)

structure contextMatch {Γ : LLVMCtxt} {Δ : RISCVCtxt} (V₁ : Γ.Valuation) (V₂ : Δ.Valuation) where
  ctxtEq :  convertLLVMContextToRiscv (evalContextLLVM Γ V₁)  = (evalContextRiscv Δ V₂)


theorem eq_of_contextMatch_of_eq {Γ : LLVMCtxt} {Δ : RISCVCtxt} {V₁ : Γ.Valuation} {V₂ : Δ.Valuation}
  (h : contextMatch V₁ V₂) (hV₁ : V₁ ⟨i, hiV1⟩ = some x) : V₂ ⟨i, hiV2⟩ = x := sorry


def riscv_add :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.add" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]

theorem denote_riscv_add_eq_add (v1 v2 : BitVec 64)
  (h1 : (V ⟨0, by rfl⟩) = v1)
  (h2 : (V ⟨1, by rfl⟩) =  v2) :
  riscv_add.denote V =  (v1 + v2) := by
unfold riscv_add
simp_peephole
simp [HVector.getN, HVector.get]
repeat rw [Ctxt.Var.last]
rw [h1] -- TODO: correct normal forms and simprocs
rw [RV64.RTYPE_pure64_RISCV_ADD]
rw [BitVec.add_eq]
congr

def llvm_add :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add %Y, %X : i64
      llvm.return %v1 : i64
}]

theorem denote_llvm_add_eq_add_of_eq_some_of_eq_some
  (h1 : (V ⟨0, by rfl⟩) = some v1)
  (h2 : (V ⟨1, by rfl⟩) = some v2) :
  llvm_add.denote V = some (v1 + v2) := by
unfold llvm_add
simp_peephole
simp [HVector.getN, HVector.get]
rw [Ctxt.Var.last]
rw [h2, h1]
simp [LLVM.add] -- TODO: non-confluent simp-set.
rw [LLVM.add?_eq]

theorem denote_llvm_add_eq_none_of_eq_none_left
  (h1 : (V ⟨0, by rfl⟩) = none) :
  llvm_add.denote V = none := by
unfold llvm_add
simp_peephole
simp [HVector.getN, HVector.get]
rw [Ctxt.Var.last]
rw [h1]
simp [LLVM.add] -- TODO: non-confluent simp-set.

theorem denote_llvm_add_eq_none_of_eq_none_right
  (h2 : (V ⟨1, by rfl⟩) = none) :
  llvm_add.denote V = none := by
unfold llvm_add
simp_peephole
simp [HVector.getN, HVector.get]
rw [Ctxt.Var.last]
rw [h2]
simp [LLVM.add] -- TODO: non-confluent simp-set.

theorem valuation_eq_some_of_llvm_add_denote_eq_some
  (h : llvm_add.denote V = some x) :
    ∃ (v1 v2 : BitVec 64),
      (V ⟨0, by rfl⟩ = some v1) ∧ (V ⟨1, by rfl⟩ = some v2) ∧ (v1 + v2 = x)  := by
  generalize hv1? : V ⟨0, by rfl⟩ = v1?
  generalize hv2? : V ⟨1, by rfl⟩ = v2?
  cases v1?
  case none =>
    simp
    have := denote_llvm_add_eq_none_of_eq_none_left hv1?
    rw [h] at this
    contradiction
  case some v1 =>
    cases v2?
    case none =>
      simp
      have := denote_llvm_add_eq_none_of_eq_none_right hv2?
      rw [h] at this
      contradiction
    case some v2 =>
      exists v1
      exists v2
      simp
      have := denote_llvm_add_eq_add_of_eq_some_of_eq_some hv1? hv2?
      rw [h] at this
      injection this with this
      rw [this]

theorem see_LLVM3 (V₁) (V₂) (h : contextMatch V₁ V₂) : -- i know that at core both contexts map to the same values, none values are filitered out
    ∀ x, (llvm_add.denote V₁ = some x → riscv_add.denote V₂ = x) := by
    let ⟨val_refines⟩ := h
    --simp_alive_meta
    cases h1 :  (llvm_add.denote V₁) with
    | none =>
      intros x hx
      simp at hx
    | some val =>
      intros x hx
      injection hx with hx
      subst hx
      have := valuation_eq_some_of_llvm_add_denote_eq_some h1
      obtain ⟨v1, v2, hv1, hv2, hadd⟩ := this
      rw [denote_riscv_add_eq_add v1 v2]
      · rw [hadd]
      · -- use context match
        sorry
      · -- use context match
        sorry
