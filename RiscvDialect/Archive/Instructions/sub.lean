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



-- section for implementing subtraction

def riscv_sub :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.sub" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]

def llvm_sub :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64, %Z : i64 ):
      %v1 = llvm.sub %Y, %X : i64
      llvm.return %v1 : i64
}]

/-
toughts on how to implement a more generalized version,
use i and j aka assume the accesing them returns some
-/
theorem denote_llvm_sub_eq_some_of_sub_some
  (h1 : (V ⟨0, by rfl⟩) = some v1)
  (h2 : (V ⟨1, by rfl⟩) = some v2) : llvm_sub.denote V = some (v1 - v2) := by
  unfold llvm_sub
  simp_peephole
  rw [Ctxt.Var.last]
  simp [HVector.get]
  rw [h2,Ctxt.Var.last, h1]
  rfl

theorem denote_llvm_sub_eq_none_of_none_left
  (h1 : (V ⟨0, by rfl⟩) = none)
    : llvm_sub.denote V = none := by
    unfold llvm_sub
    simp_peephole
    rw [Ctxt.Var.last]
    simp [HVector.get]
    rw [Ctxt.Var.last]
    rw [h1]
    rfl

theorem denote_llvm_sub_eq_none_of_none_right
  (h2 : (V ⟨1, by rfl⟩) = none)
 : llvm_sub.denote V = none := by
  unfold llvm_sub
  simp_peephole
  rw [Ctxt.Var.last]
  simp [HVector.get]
  rw [Ctxt.Var.last]
  rw [h2]
  simp [LLVM.sub]


theorem denote_riscv_sub_eq_sub (v1 v2 : BitVec 64)
  (h1 : (V ⟨0, by rfl⟩) = v1)
  (h2 : (V ⟨1, by rfl⟩) =  v2) :
  riscv_sub.denote V =  (v1 - v2) := by
unfold riscv_sub
simp_peephole
simp [HVector.getN, HVector.get]
repeat rw [Ctxt.Var.last]
rw [h1] -- TODO: correct normal forms and simprocs
rw [RV64.RTYPE_pure64_RISCV_SUB]
rw [BitVec.sub_eq] -- look up this lemma
congr

-- proof flow:
  -- given this : llvm_sub.denote V₁ = some val there must be two variables such that both are some and they eval to some value x
  -- there assuming the above I show that there must exist such two other variables : valuation_eq_some_of_llvm_sub_denoe_eq_some
  -- showing that llvm_sub = some and via case distinction that both variables in context must be some by proofing all the none cases

-- idea take statement from the proof and split it up and proof sequence wise
theorem valuation_eq_some_of_llvm_sub_denoe_eq_some  (h: llvm_sub.denote V = some x) :
    ∃ (v1 v2 : BitVec 64), ((V ⟨0, by rfl⟩ = some v1) ∧ (V ⟨1, by rfl⟩ = some v2 ) ∧ (v1 - v2 = x) )
  := by
  --rw [denote_llvm_sub_eq_some_of_sub_some] at h
  generalize hv1?:  V ⟨0, ⋯⟩ = v1?
  generalize hv2?: V ⟨1, ⋯⟩ = v2?
  cases v1?
  case none =>
    have := denote_llvm_sub_eq_none_of_none_left hv1?
    rw [this] at h
    contradiction
  case some v1 =>
    cases v2?
    case none =>
      have := denote_llvm_sub_eq_none_of_none_right hv2?
      rw [this] at h
      contradiction
    case some v2 =>
      exists v1
      exists v2
      -- careful : having the x existenitally qualified as i first did is wrong
      simp
      have := denote_llvm_sub_eq_some_of_sub_some hv1? hv2?
      rw [h] at this
      injection this with this
      rw [this]
      -- show that riscv subtraction is actual bitvec subtraction using the variables



    -- case where v1? is none
    -- if i just write simp it would be give me false evenought i can proof it , use other hyptoheis
    -- use the lemma is llvm_sub denote is some it must be using the first nad 2nd variable and they are some





-- this is the version with the straight one on one mapping between the llvm ir context and riscv context
theorem translate_sub (V₁)(V₂) (h : contextMatchLLVMRISCV V₁ V₂ binOpHom_i_to_i) :
 ∀ x, (llvm_sub.denote V₁ = some x → riscv_sub.denote V₂ = x)
 := by
    intros x
    cases h1 : llvm_sub.denote V₁ with
    | none =>
        intros hx
        simp at hx
    | some val =>
      intros hx
      injection hx with hx
      subst hx
      -- use this hyptohesis : llvm_sub.denote V₁ = some val
      have := valuation_eq_some_of_llvm_sub_denoe_eq_some h1 --intorduces new proofs etc
      obtain  ⟨v1, v2, hv1, hv2, val ⟩ := this
      rw [denote_riscv_sub_eq_sub v1 v2]
      . rw [val]
      . apply eq_of_contextMatch_of_eq binOpHom_i_to_i
        . exact h
        .rfl
        . simp [binOpHom_i_to_i]
          rw [Ctxt.Var.last]
          exact hv1
      . apply eq_of_contextMatch_of_eq binOpHom_i_to_i
        . exact h
        . rfl
        . simp [binOpHom_i_to_i]
          rw [Ctxt.Var.last]
          exact hv2

-- to do context match
theorem translate_sub_reverse (V₁)(V₂) (h : contextMatchLLVMRISCV V₁ V₂ binOpHom_i_to_modi) :
 ∀ x, (llvm_sub.denote V₁ = some x → riscv_sub.denote V₂ = x)
 := by
    intros x
    cases h1 : llvm_sub.denote V₁ with
    | none =>
        intros hx
        simp at hx
    | some val =>
      intros hx
      injection hx with hx
      subst hx
      -- use this hyptohesis : llvm_sub.denote V₁ = some val
      have := valuation_eq_some_of_llvm_sub_denoe_eq_some h1 --intorduces new proofs etc
      obtain  ⟨v1, v2, hv1, hv2, val ⟩ := this
      rw [denote_riscv_sub_eq_sub v2 v1]
      . rw [val]
      . apply eq_of_contextMatch_of_eq binOpHom_i_to_modi
        . exact h
        .rfl
        . simp [binOpHom_i_to_modi]
          rw [Ctxt.Var.last]
          exact hv2
      . apply eq_of_contextMatch_of_eq binOpHom_i_to_modi
        . exact h
        . rfl
        . simp [binOpHom_i_to_modi]
          rw [Ctxt.Var.last]
          exact hv1
