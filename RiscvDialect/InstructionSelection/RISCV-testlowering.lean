
import SSA.Core.Tactic
import SSA.Core.ErasedContext
import SSA.Core.HVector
import SSA.Core.EffectKind
import SSA.Core.Util
import SSA.Projects.InstCombine.LLVM.PrettyEDSL
--import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForLean
import Lean
import SSA.Core.Framework
import SSA.Core.Tactic
import SSA.Core.Util
import SSA.Core.MLIRSyntax.GenericParser
import SSA.Core.MLIRSyntax.EDSL
import SSA.Projects.InstCombine.Tactic
import Mathlib.Tactic.Ring
-- import RiscvDialect.Peephole_Optimizations.RiscVRefinement
import Qq
import Lean
import Mathlib.Logic.Function.Iterate
import SSA.Core.Framework
import SSA.Core.Tactic
import SSA.Core.Util
import SSA.Core.MLIRSyntax.GenericParser
import SSA.Core.MLIRSyntax.EDSL
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.DCE.DCE
import Mathlib.Tactic.Ring
import RiscvDialect.RISCV64.all

open MLIR AST
open RISCV64
open DCE
open RISCVExpr

/-- Tthis file contains tools to lowering riscv instructions to other riscv instructions. Also includes a skeleton of
a verifed lowering from riscv to riscv but where simple just to get familar with how to modell such translations.
-/


def transalte (op :RISCV64.Op) : RISCV64.Op :=
  match op with
  | .add => .sub
  | .sub => .add
  | .mul => .mul
  | .div => .div
  | .and => .and
  | .or => .or
  | _ => op -- add more operations as needed



#check Ctxt
#check Expr.mk

def instruction_translation_refinement {Γ : List Ty } (e : Expr RV64 Γ .pure .bv) : { e' : Expr RV64 Γ .pure .bv //  e.denote = e'.denote } :=
   match e with
  | Expr.mk
    (.add)
    (_)
    (_)
    (ls)
    (_) =>  ⟨ Expr.mk
    (op := RISCV64.Op.add)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := ls)
    (regArgs := .nil), by rfl ⟩
  | e  => ⟨ e , by rfl ⟩



  /- match e with
  | Expr.mk
    (add)
    (_)
    (_)
    (ls)
    (_) =>  ⟨ Expr.mk
    (op := RISCV64.Op.add)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := ls)
    (regArgs := .nil), by rfl ⟩
  | e  => ⟨ e , by rfl ⟩ -/

def instruction (e : Expr RV64 Γ .pure .bv) :  Expr RV64 Γ .pure .bv :=
  match e with
  | Expr.mk
    (.add)
    (_)
    (_)
    (ls)
    (_) =>  Expr.mk
    (op := Op.sub)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := ls)
    (regArgs := .nil)
  | e  =>  e


theorem eq_denote {Γ : Ctxt RV64.Ty}{V : Ctxt.Valuation Γ} {e e' :Expr RV64 Γ .pure .bv} {c' c₁ :  Com RV64 (Ctxt.snoc Γ Ty.bv) EffectKind.pure .bv} (h1: e.denote = e'.denote ) (h2: c'.denote = c₁.denote): (Com.var e c').denote V = (Com.var e' c₁).denote V
:= by
  dsimp [Com.denote]
  rw [h2]
  rw [h1]

/--this rewrites riscv into the same riscv instruction and is proven to be correct.
The purpose of this was to understand the strucutre on how to write lowerings that are proven to be correct.
-/

def loweringR {Γ : Ctxt Ty} (com : Com RV64 Γ .pure .bv)(fuel : Nat) :  { com' :  Com RV64 Γ .pure .bv //  com.denote = com'.denote } :=
  match com with
  | Com.ret x  => ⟨ Com.ret x , by rfl ⟩
  | Com.var (e) c' =>
  let ⟨c₁, hc₁⟩ := loweringR c' (fuel - 1)
  have hc₁ : c'.denote = c₁.denote := by
    exact hc₁
  let e' := (instruction_translation_refinement e).val
  let he := (instruction_translation_refinement e).property
  ⟨Com.var e' c₁ ,
  by
    funext V
    dsimp [Com.denote]
    rw [hc₁]
    rw [he]
    ⟩

def lowering {Γ : Ctxt Ty} (com : Com RV64 Γ .pure .bv):   Com RV64 Γ .pure .bv  :=
  match com with
  | Com.ret x  =>  Com.ret x
  | Com.var (e) c' =>
      let e' := (instruction e)
      Com.var (e') (lowering c')


--Test examples to see that the lowering actually works.
def test_lowering2 : Com RV64 [.bv] .pure .bv :=
  [RV64_com| {
  ^entry (%0: !i64 ):
    %1 = "RV64.add" (%0, %0) : ( !i64, !i64 ) -> (!i64)
    %2 = "RV64.add" (%1, %1) : ( !i64, !i64 ) -> (!i64)
    %3 = "RV64.add" (%2, %2) : ( !i64, !i64 ) -> (!i64)
    "return" (%3) : ( !i64) -> ()
}]

def test_lowering2Result : Com RV64 [.bv] .pure .bv :=
  [RV64_com| {
  ^entry (%0: !i64 ):
    %1 = "RV64.sub" (%0, %0) : ( !i64, !i64 ) -> (!i64)
    %2 = "RV64.sub" (%1, %1) : ( !i64, !i64 ) -> (!i64)
    %3 = "RV64.sub" (%2, %2) : ( !i64, !i64 ) -> (!i64)
    "return" (%3) : ( !i64) -> ()
}]
#check Com
-- def comSize02 := comSize test_lowering2
def test_lowering22 : Com RV64 [.bv] .pure .bv := (lowering test_lowering2)

theorem bigLoweringCorrect : test_lowering22 = test_lowering2Result := by
  unfold test_lowering22 test_lowering2Result  lowering
  simp
  native_decide

def test_lowering : Com RV64 [.bv] .pure .bv :=
  [RV64_com| {
  ^entry (%0: !i64 ):
    %1 = "RV64.add" (%0, %0) : ( !i64, !i64 ) -> (!i64)
    "return" (%1) : ( !i64) -> ()
}]


def test : lowering  [RV64_com| {
  ^entry (%0: !i64, %2: !i64 ):
    %1 = "RV64.add" (%0, %0) : ( !i64, !i64 ) -> (!i64)
    "return" (%1) : ( !i64) -> ()
}]  =
  [RV64_com| {
  ^entry (%reg1: !i64, %reg2: !i64 ):
    %1 = "RV64.sub" (%reg1, %reg1) : ( !i64, !i64 ) -> (!i64)
    "return" (%1) : ( !i64) -> ()
}] := by
  unfold lowering
  simp
  native_decide

def com_eq_IR : [RV64_com| {
  ^entry (%0: !i64 ):
    %1 = "RV64.sub" (%0, %0) : ( !i64, !i64 ) -> (!i64)
    "return" (%1) : ( !i64) -> ()
}] = Com.var (sub ⟨0, by simp [Ctxt.snoc]⟩ ⟨0, by simp [Ctxt.snoc]⟩) (Com.ret ⟨0, by simp [Ctxt.snoc]⟩) :=
  by
  native_decide

def test_explicit :
  lowering  [RV64_com| {
  ^entry (%0: !i64 ):
    %1 = "RV64.add" (%0, %0) : ( !i64, !i64 ) -> (!i64)
    "return" (%1) : ( !i64) -> ()
}] = Com.var (sub ⟨0, by simp [Ctxt.snoc]⟩ ⟨0, by simp [Ctxt.snoc]⟩) (Com.ret ⟨0, by simp [Ctxt.snoc]⟩)
  := by
  unfold lowering
  simp
  unfold instruction
  native_decide


-- TO UNDERSTAND HOW THE CONTEXT MOVES
def test_explicit_context :
  lowering  [RV64_com| {
  ^entry (%0: !i64, %2 : !i64 ): -- context grows from left to right aka gets added from left to right and thus: %0 is index 1 and %2 is index 0
    %1 = "RV64.add" (%0, %0) : ( !i64, !i64 ) -> (!i64) -- regarding context : left most has highst index
    "return" (%1) : ( !i64) -> ()
}] = Com.var (sub ⟨1, by simp [Ctxt.snoc]⟩ ⟨1, by simp [Ctxt.snoc]⟩) (Com.ret ⟨0, by simp [Ctxt.snoc]⟩)
  := by
  unfold lowering
  simp
  unfold instruction
  native_decide
