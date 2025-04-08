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


def LLVMCtxt := Ctxt InstCombine.Ty
def RISCVCtxt := Ctxt toRISCV.Ty

-- contains some of my attempts to define context mapping. might be able to see what I've done wrong in some months
/-
def CtxtRefines (Γ : Ctxt LLVM.Ty) (Δ : Ctxt RV64.Ty) : Type :=
  (Δ.Var .bv) → Γ.Var (.bitvec 64)




def toLLVM : RV64.Ty → InstCombine.Ty
  | .bv => .bitvec 64 -- keep in mind the InstCombine Ty is an otion bit vec

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

def allVarsFromDialect (Γ : Ctxt Ty) :=
  (List.range Γ.length).map (fun i => ⟨i, by sorry⟩)
-/
/-
def allVarsRiscv (Δ : Ctxt (toRISCV.Ty)) : List (Δ.Var .bv) :=
  (List.range Δ.length).map (fun i =>
    ⟨i, by sorry⟩)

def allVarsLLVM (Γ : Ctxt (InstCombine.Ty)) : List (Γ.Var (.bitvec 64)) :=
  (List.range Γ.length).map (fun i =>
    ⟨i,by  sorry⟩)

-- type of var is a DeBruijn index meaning a nat and a proof that the nat has the correspodning type
def evalContextRiscv (Δ : RISCVCtxt) (V₁ : Δ.Valuation) : List (BitVec 64) :=
  (allVarsRiscv Δ).map (@V₁ _)


-- type of var is a DeBruijn index meaning a nat and a proof that the nat has the correspodning type
def evalContextLLVM(Γ : Ctxt (InstCombine.Ty)) (V₁ : Γ.Valuation) : List (Option (BitVec 64)) :=
  (allVarsLLVM Γ).map (@V₁ _)
-/

-- The french trick of converting a theorem into a definition.
-- Grothendieck!
-- lemmas that helped me in proof engineering

-- to tell Lean that all elements of toRISCV.Ty actually have type .bv because toRISCV Dialect only models one type.
theorem toRISCV.Ty.isSubsingleton (t : toRISCV.Ty) : t = toRISCV.Ty.bv := by
  cases t; rfl -- cases on the constructor of t and because its its only one element is follows by reflection.

-- proof that all elements Riscv have the type bitvector .bv
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

-- generic over the type universes
structure HHom {TyΓ TyΔ} (Γ : Ctxt TyΓ) (Δ : Ctxt TyΔ) where
  {tyΓ : TyΓ}
  {tyΔ : TyΔ}
  toFun : Γ.Var tyΓ → Δ.Var tyΔ -- how each variable in the context TyΓ is mapped to a variable in TyΔ

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
  may map to the same LLVM *virtual* register. --ASK
-/
--structure contextMatchHom {Γ : LLVMCtxt} {Δ : RISCVCtxt} (VΓ : Γ.Valuation) (VΔ : Δ.Valuation) (hom : HHom Δ Γ) where
-- theorem_foo: (f <something complex>= y)
-- theorem_foo': (x = <something complex>) → (f x = y)
-- apply theorem_foo |- f <something different but equivalent to something complex> = y
-- apply theorem_foo' |- f <something different but equivalent to something complex> = y
--   |- <something different but equivalent to something complex> = <something complex>
-- *Fording*: Henry ford
-- > you can have any car color you like, as long as it's black!
/-
A matched context between LLVM and RISCV for arbitrary LLVM context Γ and arbitrary RISCV context Δ.
-/

-- RISC-V and LVVM specific

-- this is the core of cross-dialect translation, need to generalize it to arbitrary contexts
-- is already generic over contexts (not over types)
structure contextMatchLLVMRISCV {Γ : LLVMCtxt} {Δ : RISCVCtxt}
    (V₁ : Γ.Valuation) (V₂ : Δ.Valuation)
    (hom : Δ.Var toRISCV.Ty.bv → Γ.Var (InstCombine.Ty.bitvec 64)) where
  ctxtEq : ∀ {vΔ : Δ.Var (toRISCV.Ty.bv)} {vΓ : Γ.Var (InstCombine.Ty.bitvec 64)}
    (h : vΓ = hom vΔ) {x : BitVec 64}, (V₁ vΓ = some x) → V₂ vΔ = x

-- proving that if LLVM has a non-poison value then in RISC-V it is a register value
theorem eq_of_contextMatch_of_eq {Γ : LLVMCtxt} {Δ : RISCVCtxt}
    {VΓ : Ctxt.Valuation Γ}
    {VΔ : Ctxt.Valuation Δ}
    (hom : Δ.Var toRISCV.Ty.bv → Γ.Var (InstCombine.Ty.bitvec 64))
    (hV : contextMatchLLVMRISCV VΓ VΔ hom)
    (vΔ : Δ.Var toRISCV.Ty.bv) {vΓ : Γ.Var (InstCombine.Ty.bitvec 64)}
    (hv : vΓ = hom vΔ) -- maps between the indicies
    (hVΓ : VΓ vΓ = some x) : VΔ vΔ = x := by
    apply hV.ctxtEq -- introduce new subgoals by using that the conclusion of the goal matches and the proofing the assumptions
    · rfl
    · rw [← hv]; use hVΓ

  /- convertLLVMContextToRiscv (evalContextLLVM Γ V₁)  = (evalContextRiscv Δ V₂) -/

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


-- next goal is to define refinement for an aribtraty context but for that must first understand the existing contexts
