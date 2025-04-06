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

set_option Elab.async false

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

/-
-- for a valuation, we need to evaluate the Lean `Type` corresponding to a `Ty`
variable [TyDenote Ty]

/-- A valuation for a context. Provide a way to evaluate every variable in a context. -/
def Valuation (Γ : Ctxt Ty) : Type :=
  ⦃t : Ty⦄ → Γ.Var t → (toType t)

/-- A valuation for a context. Provide a way to evaluate every variable in a context. -/
def Valuation.eval {Γ : Ctxt Ty} (VAL : Valuation Γ) ⦃t : Ty⦄ (v : Γ.Var t) : toType t :=
    VAL v


def evalContextRiscv (Δ : RISCVCtxt) (VAL : Valuation Δ) : List (BitVec 64) :=
  Δ.vars.map (λ ⦃t⦄ (v : Δ.Var t) => VAL.eval v)

def allVars (Δ : Ctxt toRISCV.Ty) : List (Δ.Var .bv) :=
  (List.range Δ.length).filterMap fun i =>
    match Δ.get? i with
    | some .bv => some ⟨i, rfl⟩
    | _        => none

 (List.range Δ.length).map fun i =>
    ⟨i, by sorry
    ⟩


-/



-- def allVarsFromDialect (Γ : Ctxt Ty) :=
--   (List.range Γ.length).map (fun i => ⟨i, sorry⟩)


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

-- The french trick of converting a theorem into a definition.
-- Grothendieck!

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

theorem toRISCV.Ty.isSubsingleton (t : toRISCV.Ty) : t = toRISCV.Ty.bv := by
  cases t; rfl

instance : Subsingleton (toRISCV.Ty) where
    allEq := by
      intros a b
      rw [toRISCV.Ty.isSubsingleton a, toRISCV.Ty.isSubsingleton b]


/--
A Heterogeneous morphism of contexts.
This maps variables in context `Γ` (with variables drawn from a type universe `TyΓ`)
into variable in a context `Delta` (with variables drawn from a type universe `TyΔ`).
We do not stipulate that a raw `HHom` is well-formed, and we allow mappings
between different types in general.
This is necessary to model cases such as LLVM → RISCV, where LLVM has a richer domain of values
that includes poison, while raw RISCV registers are pure bitvectors.
-/
structure HHom {TyΓ TyΔ} (Γ : Ctxt TyΓ) (Δ : Ctxt TyΔ) where
  {tyΓ : TyΓ}
  {tyΔ : TyΔ}
  toFun : Γ.Var tyΓ → Δ.Var tyΔ

/--
A Uniform heterogeneous morphism of contexts,
which stipulates that the denotation of the source and target types must be equal.
This exists to allow lifting a `Hom` into a `HHom` without forgetting that we started from a `Hom`.
Recall that a `Hom` forces the source and target types to be equal. Hence, we remember this equality
with `htyEq` when lifting a `Hom` into a `UniformHHom`
-/
structure UniformHHom {TyΓ} {TyΔ} (Γ : Ctxt TyΓ) (Δ : Ctxt TyΔ) [TyDenote TyΓ] [TyDenote TyΔ] extends HHom Γ Δ where
  htyEq : TyDenote.toType tyΓ = TyDenote.toType tyΔ



/--
We follow the yoga of categories,
where we do not ask for context *equality*, but only for a map from context Δ into context Γ.
See that this provides a lot of flexibility:
- LLVM (Γ) can have many more variables than RISCV (Δ), which can be safely ignored.
- Multiple RISCV variables (Δ) can map to the *same* LLVM variable (Γ).
  This is important for e.g. register allocation, because multiple physical registers at different points in program time
  may map to the same LLVM *virtual* register.
-/
structure contextMatchHom {Γ : LLVMCtxt} {Δ : RISCVCtxt} (VΓ : Γ.Valuation) (VΔ : Δ.Valuation) (hom : HHom Δ Γ) where


-- theorem_foo: (f <something complex>= y)
-- theorem_foo': (x = <something complex>) → (f x = y)
-- apply theorem_foo |- f <something different but equivalent to something complex> = y
-- apply theorem_foo' |- f <something different but equivalent to something complex> = y
--   |- <something different but equivalent to something complex> = <something complex>
-- *Fording*: Henry ford
-- > you can have any car color you like, as long as it's black!
/--
A matched context between LLVM and RISCV for arbitrary LLVM context Γ and arbitrary RISCV context Δ.
-/
structure contextMatchLLVMRISCV {Γ : LLVMCtxt} {Δ : RISCVCtxt}
    (V₁ : Γ.Valuation) (V₂ : Δ.Valuation)
    (hom : Δ.Var toRISCV.Ty.bv → Γ.Var (InstCombine.Ty.bitvec 64)) where
  ctxtEq : ∀ {vΔ : Δ.Var (toRISCV.Ty.bv)} {vΓ : Γ.Var (InstCombine.Ty.bitvec 64)}
    (h : vΓ = hom vΔ) {x : BitVec 64}, (V₁ vΓ = some x) → V₂ vΔ = x

theorem eq_of_contextMatch_of_eq {Γ : LLVMCtxt} {Δ : RISCVCtxt}
    {VΓ : Ctxt.Valuation Γ}
    {VΔ : Ctxt.Valuation Δ}
    (hom : Δ.Var toRISCV.Ty.bv → Γ.Var (InstCombine.Ty.bitvec 64))
    (hV : contextMatchLLVMRISCV VΓ VΔ hom) (vΔ : Δ.Var toRISCV.Ty.bv) {vΓ : Γ.Var (InstCombine.Ty.bitvec 64)}
    (hv : vΓ = hom vΔ)
    (hVΓ : VΓ vΓ = some x) : VΔ vΔ = x := by
    apply hV.ctxtEq
    · rfl
    · rw [← hv]; use hVΓ

  /- convertLLVMContextToRiscv (evalContextLLVM Γ V₁)  = (evalContextRiscv Δ V₂) -/

-- learned that it is for a specifc context
-- goal cases analysis on the context aka what does it mean first that context match
--- have the same lenght and whenever there is a riscv vector there must be the corresponding llvm some vecotr


-- ASK
-- (V : Ctxt.Valuation [InstCombine.Ty.bitvec 64, InstCombine.Ty.bitvec 64])
-- theorem eq_of_contextMatch_of_eq_zero
--     {V₁ : Ctxt.Valuation [InstCombine.Ty.bitvec 64, InstCombine.Ty.bitvec 64]}
--     {V₂ : Ctxt.Valuation [toRISCV.Ty.bv, toRISCV.Ty.bv]}
--     (h : contextMatch V₁ V₂)
--     (hV₁ : V₁ ⟨0, by rfl⟩ = some x) : V₂ ⟨0, rfl⟩ = x := by
--     apply h.ctxtEq (v₁ := ⟨0, by rfl⟩)
--     · rfl
--     · exact hV₁

-- theorem eq_of_contextMatch_of_eq_one
--     {V₁ : Ctxt.Valuation [InstCombine.Ty.bitvec 64, InstCombine.Ty.bitvec 64]}
--     {V₂ : Ctxt.Valuation [toRISCV.Ty.bv, toRISCV.Ty.bv]}
--     (h : contextMatch V₁ V₂)
--     (hV₁ : V₁ ⟨1, by rfl⟩ = some x) : V₂ ⟨1, rfl⟩ = x := by
--     apply h.ctxtEq (v₁ := ⟨1, by rfl⟩)
--     · rfl
--     · exact hV₁


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

def addHom (vΔ: Ctxt.Var [toRISCV.Ty.bv, toRISCV.Ty.bv] toRISCV.Ty.bv) :
  Ctxt.Var [InstCombine.Ty.bitvec 64, InstCombine.Ty.bitvec 64] (InstCombine.Ty.bitvec 64) :=
⟨vΔ.val, by -- 0 -> 0, 1 -> 1
  have := vΔ.prop
  have : vΔ.val ≤ 1 := by
    by_contra h
    simp at h
    have hcontra : Ctxt.get? [Ty.bv, Ty.bv] vΔ.val = none := by
      simp [Ctxt.get?] -- TODO: write theorems
      omega
    rw [hcontra]at this
    contradiction
  have : vΔ.val = 0 ∨ vΔ.val = 1 := by omega
  rcases this with hv | hv
  · simp [hv]
  · simp [hv]⟩

theorem translate_add (V₁) (V₂) (h : contextMatchLLVMRISCV V₁ V₂ addHom) : -- i know that at core both contexts map to the same values, none values are filitered out
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
        apply eq_of_contextMatch_of_eq addHom
        · exact h
        · simp [addHom]
          rfl
        · rw [Ctxt.Var.last]
          exact hv1
      · -- use context match
        apply eq_of_contextMatch_of_eq addHom
        · exact h
        · simp [addHom]; rfl
        · rw [Ctxt.Var.last]; exact hv2

-- section for implementing subtraction

def riscv_sub :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.sub" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]

def llvm_sub :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.sub %Y, %X : i64
      llvm.return %v1 : i64
}]
-- why doesn't this type check --> had to refer to a specifc context
theorem denote_llvm_sub_eq_some_of_sub_of_some_explicit (V : Ctxt.Valuation [InstCombine.Ty.bitvec 64, InstCombine.Ty.bitvec 64])
  (h1 : (V ⟨0, by rfl⟩) = some v1)
  (h2 : (V ⟨1, by rfl⟩) = some v2) : llvm_sub.denote V = some (v1 + v2) := by sorry

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

  . -- case where v1? is some

theorem translate_sub (V₁)(V₂) (h : contextMatch V₁ V₂) :
  ∀ x, (llvm_sub.denote V₁ = some x → riscv_sub.denote V₂ = x) := by
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
    . sorry -- to do context match
    . sorry -- to do context match

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
