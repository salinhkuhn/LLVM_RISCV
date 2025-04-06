import RiscvDialect.RDialect
import RiscvDialect.RefinementDialect
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

set_option Elab.async false

def riscv_add :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.add" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]

theorem denote_riscv_add_eq_add (rv1 rv2 : BitVec 64)
  (h1 : (V ⟨0, by rfl⟩) = rv1)
  (h2 : (V ⟨1, by rfl⟩) =  rv2) :
  riscv_add.denote V =  (rv1 + rv2) := by
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

def llvm_add_poison :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64, %Z : i64 ):
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

-- how to map the single indices between the contexts
-- here the morhpism for addition is one to one

-- the following mappping one-on-one mapping respecting the correct order such that
-- [x1, x2] --> [%X, %Y] such that  x1.get = %X, x2.get = %Y
def binOpHom_i_to_i (vΔ: Ctxt.Var [toRISCV.Ty.bv, toRISCV.Ty.bv] toRISCV.Ty.bv) :
  Ctxt.Var [InstCombine.Ty.bitvec 64, InstCombine.Ty.bitvec 64] (InstCombine.Ty.bitvec 64) :=
⟨vΔ.val, by -- 0 -> 0, 1 -> 1
  have := vΔ.prop
  have : vΔ.val ≤ 1 := by -- good example of proof by contradiction
    by_contra h
    simp at h
    have hcontra : Ctxt.get? [Ty.bv, Ty.bv] vΔ.val = none := by
      simp [Ctxt.get?] -- TODO: write theorems
      omega
    rw [hcontra]at this
    contradiction
  have : vΔ.val = 0 ∨ vΔ.val = 1 := by omega
  rcases this with hv0 | hv1
  · simp [hv0]
  · simp [hv1]⟩

-- mapping with inverted context correspondance
-- [x1, x2] --> [%X, %Y] such that  x1.get = %Y, x2.get =%X
def binOpHom_i_to_modi (vΔ: Ctxt.Var [toRISCV.Ty.bv, toRISCV.Ty.bv] toRISCV.Ty.bv) :
   Ctxt.Var [InstCombine.Ty.bitvec 64, InstCombine.Ty.bitvec 64] (InstCombine.Ty.bitvec 64) :=
   -- knowing Δ.val = 0 v 1 we have that inverted mapping of 0 to 1 and 1 to 0
  ⟨1 - vΔ.val, by
  have := vΔ.prop -- give me the proof that Δ.val is of type toRISCV.Ty.bv
  have : vΔ.val ≤ 1 := by
    by_contra h
    simp at h
    have hcontra : Ctxt.get? [Ty.bv, Ty.bv] vΔ.val = none := by
      simp [Ctxt.get?]
      omega
    rw [hcontra] at this
    contradiction
  have : (1 - vΔ.val) = 0 ∨ (1 - vΔ.val) = 1 := by omega
  rcases this with h1 | h0
  . simp [h1]
  . simp [h0]
   ⟩ -- proof that it is actually of the type RISCV.Ty.bv

-- first value is poison and not mapped to an actual value

/- this establish a homomorphism defined for our use case as follows:
    [x1, x2] --> [%X, %Y (none), %Z] such that  x1.get = %X, x2.get =%Z
-/
-- cant be handled by the llvm instructions yet bc their signature expect to only have a context of lenght 2

-- proof structure show that  is within the bounds of the riscv context and there given that we know the type of the context we get the correct llvm type
def add_Hom_llvm_poison_to_riscv  (vΔ: Ctxt.Var [toRISCV.Ty.bv, toRISCV.Ty.bv] toRISCV.Ty.bv) : Ctxt.Var [InstCombine.Ty.bitvec 64, InstCombine.Ty.bitvec 64, InstCombine.Ty.bitvec 64] (InstCombine.Ty.bitvec 64) :=
 ⟨ 2 * vΔ.val  , by
  have := vΔ.prop
  have h1 : vΔ.val ≤ 1 := by
    by_contra h1 -- assuming this holds we show that it must have the type none and therefore is contradicting our assumption
    simp at h1
    have hcontra : Ctxt.get? [toRISCV.Ty.bv, toRISCV.Ty.bv] vΔ.val = none := by
      simp [Ctxt.get?]
      omega
    rw [hcontra] at this
    contradiction
  have : (2 * vΔ.val) = 0 ∨ (2 * vΔ.val) = 2 := by omega
  rcases this with  h0 | h2
  . rw [h0]
    simp [Ctxt.get?]
  . rw [h2]
    simp [Ctxt.get?]
  ⟩

/- this establish a homomorphism defined for our use case as follows:
    [x1, x1] --> [%X, none ] such that  x1.get = %X, x2.get =%Z
-/
def add_Hom_llvm_poison_to_riscv_same (vΔ: Ctxt.Var [toRISCV.Ty.bv, toRISCV.Ty.bv] toRISCV.Ty.bv) : Ctxt.Var [InstCombine.Ty.bitvec 64, InstCombine.Ty.bitvec 64, InstCombine.Ty.bitvec 64] (InstCombine.Ty.bitvec 64) :=
   ⟨ 2 * vΔ.val  , by
  have := vΔ.prop
  have h1 : vΔ.val ≤ 1 := by
    by_contra h1 -- assuming this holds we show that it must have the type none and therefore is contradicting our assumption
    simp at h1
    have hcontra : Ctxt.get? [toRISCV.Ty.bv, toRISCV.Ty.bv] vΔ.val = none := by
      simp [Ctxt.get?]
      omega
    rw [hcontra] at this
    contradiction
  have : (2 * vΔ.val) = 0 ∨ (2 * vΔ.val) = 2 := by omega
  rcases this with  h0 | h2
  . rw [h0]
    simp [Ctxt.get?]
  . rw [h2]
    simp [Ctxt.get?]
  ⟩

theorem translate_add_straight (V₁) (V₂) (h : contextMatchLLVMRISCV V₁ V₂  binOpHom_i_to_i) : -- i know that at core both contexts map to the same values, none values are filitered out
    ∀ x, (llvm_add.denote V₁ = some x → riscv_add.denote V₂ = x) := by
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
      obtain ⟨v1, v2, hv1, hv2, val⟩ := this
      rw [denote_riscv_add_eq_add v1 v2] -- introduces new sub goals
      · rw [val]
      · -- use context match
        apply eq_of_contextMatch_of_eq binOpHom_i_to_i
        · exact h
        · simp [binOpHom_i_to_i]
          rfl
        · rw [Ctxt.Var.last]
          exact hv1
      · -- use context match
        apply eq_of_contextMatch_of_eq binOpHom_i_to_i
        · exact h
        · simp [binOpHom_i_to_i]; rfl
        · rw [Ctxt.Var.last]; exact hv2

-- riscv v1 is llvm v2 and rsicv v2 is llvm v1
theorem translate_add_reverse (V₁) (V₂) (h : contextMatchLLVMRISCV V₁ V₂ binOpHom_i_to_modi) : -- i know that at core both contexts map to the same values, none values are filitered out
    ∀ x, (llvm_add.denote V₁ = some x → riscv_add.denote V₂ = x) := by
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
      obtain ⟨rv1, rv2, hv1, hv2, val⟩ := this
      rw [denote_riscv_add_eq_add rv2 rv1] -- introduces new sub goals
      · rw [BitVec.add_comm]
        rw [val]
      · -- use context match
        apply eq_of_contextMatch_of_eq binOpHom_i_to_modi
        · exact h
        · simp [binOpHom_i_to_modi]
          rfl
        · rw [Ctxt.Var.last]
          exact hv2
      · -- use context match
        apply eq_of_contextMatch_of_eq binOpHom_i_to_modi
        · exact h
        · simp [binOpHom_i_to_modi]; rfl
        · rw [Ctxt.Var.last]; exact hv1

--  [x1, x2] --> [%X, %Y (none), %Z] such that  x1.get = %X, x2.get =%Z
-- the problem of modelling this is that llvm.add anyways only requires the input context to be of length 2
-- tried to implement it wtih a  broader context but the istruction only process a cpntexrt of fixed length
theorem translate_add_poison (V₁) (V₂) (h : contextMatchLLVMRISCV V₁ V₂ add_Hom_llvm_poison_to_riscv ) : -- i know that at core both contexts map to the same values, none values are filitered out
    ∀ x, (llvm_add_poison.denote V₁ = some x → riscv_add.denote V₂ = x) := by
    --simp_alive_meta
    cases h1 :  (llvm_add_poison.denote V₁) with
    | none =>
      intros x hx
      simp at hx
    | some val =>
      intros x hx
      injection hx with hx
      subst hx
      have := valuation_eq_some_of_llvm_add_denote_eq_some h1
      obtain ⟨rv1, rv2, hv1, hv2, val⟩ := this
      rw [denote_riscv_add_eq_add rv2 rv1] -- introduces new sub goals
      · rw [BitVec.add_comm]
        rw [val]
      · -- use context match
        apply eq_of_contextMatch_of_eq addHom_i_to_modi
        · exact h
        · simp [addHom_i_to_modi]
          rfl
        · rw [Ctxt.Var.last]
          exact hv2
      · -- use context match
        apply eq_of_contextMatch_of_eq addHom_i_to_modi
        · exact h
        · simp [addHom_i_to_modi]; rfl
        · rw [Ctxt.Var.last]; exact hv1



    -- now knwoing that its some val we show that it must come from two instanciated variables
def riscv_or :=
  [RV64_com| {
  ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.or" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]

def llvm_or :=
  [llvm(64)| {
  ^bb0(%X : i64, %Y : i64):
      %v1 = llvm.or %Y, %X : i64 -- handle disjoint flag
      llvm.return %v1 : i64
  }]


theorem translate_or (V₁)(V₂) (h : contextMatch V₁ V₂) :
  ∀ x, (llvm_or.denote V₁ = some x → riscv_or.denote V₂ = x) := by sorry


def llvm_urem :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.urem %Y, %X : i64
      llvm.return %v1 : i64
  }]

def riscv_urem :=
  [RV64_com| {
  ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.remu" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]

theorem translation_urem (V₁)(V₂) (h : contextMatch V₁ V₂) :
  ∀ x, (llvm_urem.denote V₁ = some x → riscv_urem.denote V₂ = x) := by sorry










theorem see_LLVM2 (V₁) (V₂) (h : ValuationRefines V₁ V₂) :
    ∃ x, llvm_add.denote V₁ = some x → riscv_add.denote V₂ = x := by
    let ⟨ctxtRefines, val_refines⟩ := h
    --simp_alive_meta
    cases h1 :  (llvm_add.denote V₁) with
    | none => use 42
              intro forContradiction
              contradiction
    | some val => use val
                  intro h'
                  injection h' with h''
                  rw [←h'']
                  --simp [HVector.get, HVector.cons_get_zero]
                  unfold riscv_add
                  simp_peephole

                  unfold llvm_add at h1
                  revert h1
                  --simp_alive_meta -- TODO: remove after update
                  simp_peephole

                  intro h1
                  simp at h1

                  -- i dont know how extract the variables now , I know I can use the refinement assumptions
                  -- i now want to extract the functions in
                  -- given the result of llvm_add I know the variable used from the LLVM side must have been some x
                  -- i also know the correspoding

                  sorry
-- try to phrasde a generic rewrite


theorem see_LLVM1 (V₁) (V₂) (h : ValuationRefines V₁ V₂) :
    ∃ x, llvm_add.denote V₁ = some x → riscv_add.denote V₂ = x := by
    let ⟨ctxtRefines, val_refines⟩ := h
    cases h1 :  (llvm_add.denote V₁) with
    | none => use 42
              intro forContradiction
              contradiction
    | some val => use val
                  intro h'
                  injection h' with h''
                  rw [←h'']
                  --simp [HVector.get, HVector.cons_get_zero]
                  simp_peephole
                  unfold llvm_add at h1
                  unfold riscv_add


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

