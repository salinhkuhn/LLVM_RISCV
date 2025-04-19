import RiscvDialect.RDialect
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.LLVM.PrettyEDSL
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForLean
import Lean
import Mathlib.Tactic.Ring
import SSA.Projects.InstCombine.ForLean
import SSA.Projects.InstCombine.LLVM.EDSL
import SSA.Experimental.Bits.Fast.Reflect
import SSA.Experimental.Bits.Fast.MBA
import SSA.Experimental.Bits.FastCopy.Reflect
import SSA.Experimental.Bits.AutoStructs.Tactic
import SSA.Experimental.Bits.AutoStructs.ForLean
import Std.Tactic.BVDecide
import SSA.Core.Tactic.TacBench
import Leanwuzla

/-- this file contains explicit proofs between a llvm and riscv lowering.
-/

/- definition of refinement used in the lowerings
abbrev Com.RefinementRiscv (src tgt : Com RV64 Γ .pure t)
    (h : RV64TyDenote.toType t = BitVec 64 := by rfl) : Prop :=
  ∀ Γv, (h ▸ src.denote Γv) ⊑ᵣ (h ▸ tgt.denote Γv) -- in they end they must yield the same register value
-/

def lh_llvm (rs1 rs2: BitVec 64) : (HVector TyDenote.toType [InstCombine.Ty.bitvec 64,InstCombine.Ty.bitvec 64]) :=
          HVector.cons (some (rs2)) <| HVector.cons (some (rs1)) .nil

def lh_riscv (rs1 rs2: BitVec 64)  : HVector TyDenote.toType [toRISCV.Ty.bv,toRISCV.Ty.bv ] :=
  HVector.cons ((rs2)) <| HVector.cons ( (rs1)) .nil -- hvector from which we will create the valuation

open toRISCV
open InstCombine(LLVM)

def LLVMCtxt := Ctxt InstCombine.Ty
def RISCVCtxt := Ctxt toRISCV.Ty


def lh_llvm1 (rs1 rs2: BitVec 64) : (HVector TyDenote.toType [InstCombine.Ty.bitvec 64,InstCombine.Ty.bitvec 64]) :=
          HVector.cons (some (rs2)) <| HVector.cons (some (rs1)) .nil

def lh_riscv2 (rs1 rs2: BitVec 64)  : HVector TyDenote.toType [toRISCV.Ty.bv,toRISCV.Ty.bv ] :=
  HVector.cons ((rs2)) <| HVector.cons ( (rs1)) .nil -- hvector from which we will create the valuation


def ADD_RV64 :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.add" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }].denote

def ADD_LLVM :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

  def ADD_LLVM_BIG_CONTEXT :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64, %Z : i64, %W : i64):
      %v1 = llvm.add %Y, %X : i64
      llvm.return %v1 : i64
  }]

-- try to do it using exist quantifier as a help
theorem  translation_add_combined1 (x3 x4: BitVec 64) :
∃ x, ADD_LLVM (Ctxt.Valuation.ofHVector (lh_llvm x3 x4)) = some x →
      x = ADD_RV64 (Ctxt.Valuation.ofHVector (lh_riscv x3 x4)) := by
    unfold ADD_RV64 lh_riscv ADD_LLVM lh_llvm
    simp_alive_meta
    simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.add, LLVM.add?]
    unfold RV64.RTYPE_pure64_RISCV_ADD
    simp [HVector.cons_get_zero]
    use (x4 + x3)
    intro h
    injection h with h1

def HVector.llvmToRiscv {ts : List InstCombine.Ty}
  (h : HVector TyDenote.toType (ts.map (fun _ => InstCombine.Ty.bitvec 64)))
  : HVector TyDenote.toType (ts.map (fun _ => toRISCV.Ty.bv)) :=
  h.map (fun v => Option.get! v)


-- proofs that given two inputs the riscv instruction issued exactly is the same as the llvm instruction
theorem translation_add_combined (x3 x4: BitVec 64) :
    ADD_LLVM (Ctxt.Valuation.ofHVector (lh_llvm x3 x4)) = some x →
      x = ADD_RV64 (Ctxt.Valuation.ofHVector (lh_riscv x3 x4)) := by
    unfold ADD_RV64 lh_riscv ADD_LLVM lh_llvm
    simp_alive_meta
    simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.add]
    unfold RV64.RTYPE_pure64_RISCV_ADD
    simp [HVector.cons_get_zero]
    simp_alive_undef
    intro h
    injection h with h₁
    rw [← h₁]


def return_val_addL : BitVec 64 := ADD_LLVM (Ctxt.Valuation.ofHVector (lh_llvm 1 2 ))
def return_val_addR : BitVec 64 := ADD_RV64 (Ctxt.Valuation.ofHVector (lh_riscv 1 2) )
#eval return_val_addL

def OR_RV64 :=
  [RV64_com| {
  ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.or" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }].denote

def OR_LLVM :=
  [llvm(64)| {
  ^bb0(%X : i64, %Y : i64):
      %v1 = llvm.or %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

theorem translation_or (x3 x4: BitVec 64) :
  OR_LLVM (Ctxt.Valuation.ofHVector (lh_llvm x3 x4)) = some x →
   x = OR_RV64 (Ctxt.Valuation.ofHVector (lh_riscv x3 x4)) := by
  unfold OR_RV64 lh_riscv OR_LLVM lh_llvm
  simp_alive_meta -- removes the framework overheard
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.or, LLVM.or?]
  unfold RV64.RTYPE_pure64_RISCV_OR
  simp [HVector.cons_get_zero]
  intro h
  injection h with h₁
  rw [← h₁]
  bv_decide

-- ask how to get llvm into this form
def XOR_LLVM :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.xor %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

def XOR_RV64 :=
  [RV64_com| {
  ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.xor" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }].denote

theorem translation_xor (x3 x4: BitVec 64) :
  XOR_LLVM (Ctxt.Valuation.ofHVector (lh_llvm x3 x4)) = some x →
   x = XOR_RV64 (Ctxt.Valuation.ofHVector (lh_riscv x3 x4)) := by
  unfold XOR_RV64 lh_riscv XOR_LLVM lh_llvm
  simp_alive_meta
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.xor, LLVM.xor?]
  unfold RV64.RTYPE_pure64_RISCV_XOR
  simp [HVector.cons_get_zero]
  intro h
  injection h with h₁
  rw [← h₁]
  bv_decide

def shl_LLVM :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.shl %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

def shl_RV64 :=
  [RV64_com| {
  ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.sll" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }].denote

theorem translation_shl (x3 x4: BitVec 64) :
  shl_LLVM (Ctxt.Valuation.ofHVector (lh_llvm x3  x4)) = some x →
    x = shl_RV64 (Ctxt.Valuation.ofHVector (lh_riscv x3  x4)) := by
  unfold shl_LLVM shl_RV64
  simp_alive_meta
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.shl, LLVM.shl?]
  unfold RV64.RTYPE_pure64_RISCV_SLL lh_riscv lh_llvm
  simp [HVector.cons_get_zero]
  simp [Ctxt.Valuation.ofHVector]
  intro h
  split at h
  · contradiction
  · injection h with h₁
    rw [← h₁, Nat.mod_eq_of_lt (by bv_omega)]

/-
def shl_LLVM_flags := -- can have over- and underflow but in that case we return none as its poison value and we machine code the exhibit any behaviour
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add %Y, %X : i64
      llvm.return %v1 : i64
  }].denote -/

def lshr_LLVM :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.lshr %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

def lshr_RV64 :=
  [RV64_com| {
  ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.srl" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }].denote

theorem translation_lshr (x3 x4: BitVec 64) :
  lshr_LLVM (Ctxt.Valuation.ofHVector (lh_llvm x3  x4)) = some x →
    x = lshr_RV64 (Ctxt.Valuation.ofHVector (lh_riscv x3  x4)) := by
  unfold lshr_LLVM lshr_RV64
  simp_alive_meta
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.lshr, LLVM.lshr?]
  unfold RV64.RTYPE_pure64_RISCV_SRL lh_riscv lh_llvm
  simp [HVector.cons_get_zero]
  simp [Ctxt.Valuation.ofHVector]
  intro h
  split at h
  · contradiction
  · injection h with h₁
    rw [← h₁, Nat.mod_eq_of_lt (by bv_omega)]

def ashr_LLVM_ :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.ashr %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

def sra_RV64 :=
  [RV64_com| {
  ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.sra" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }].denote

theorem translation_ashr (x3 x4: BitVec 64) :
  ashr_LLVM_ (Ctxt.Valuation.ofHVector (lh_llvm x3  x4)) = some x →
    x = sra_RV64 (Ctxt.Valuation.ofHVector (lh_riscv x3  x4)) := by
  unfold ashr_LLVM_ sra_RV64
  simp_alive_meta
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.ashr, LLVM.ashr?]
  unfold RV64.RTYPE_pure64_RISCV_SRA lh_riscv lh_llvm
  simp [HVector.cons_get_zero]
  simp [Ctxt.Valuation.ofHVector]
  intro h
  split at h
  · contradiction
  . injection h with h₁
    rw [← h₁, Nat.mod_eq_of_lt (by bv_omega)]



def urem_LLVM :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.urem %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

def urem_RV64 :=
  [RV64_com| {
  ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.remu" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }].denote


theorem translation_urem  (x3 x4: BitVec 64) :
    urem_LLVM (Ctxt.Valuation.ofHVector (lh_llvm x3  x4)) = some x →
    x = urem_RV64 (Ctxt.Valuation.ofHVector (lh_riscv x3  x4)) := by
  unfold urem_LLVM urem_RV64
  simp_alive_meta
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.urem, LLVM.urem?]
  unfold RV64.REM_pure64_unsigned lh_riscv lh_llvm
  simp [HVector.cons_get_zero]
  simp [Ctxt.Valuation.ofHVector]
  native_decide
  intro h
  split at h
  · contradiction
  . injection h with h2
    rw [← h2]
    simp [h2]
    have : ¬x3.toNat = 0 := by sorry
    simp [this]
    have : x4.toNat % x3.toNat = x.toNat := by sorry

def srem_LLVM_ :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.srem %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

def ADD_LLVM_flags :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
         %v1 = llvm.add %X, %Y overflow<nsw> : i64
           llvm.return %v1 : i64
  }].denote

#check ADD_LLVM_flags
#check lh_llvm
def return_val_add : Option (BitVec 64) := ADD_LLVM_flags (Ctxt.Valuation.ofHVector (lh_llvm 1 2))
#eval return_val_add
--#eval return_val_add

def MUL_LLVM :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.mul %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

def MUL_LLVM_flags :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

def SUB_LLVM :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.sub %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

def SUB_RV64 :=
  [RV64_com| {
  ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.sub" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }].denote

-- assuming no integer overflow and underflow etc. so when llvm sub returns a value then also machine code in riscv will
theorem translation_sub (x3 x4: BitVec 64) :
  SUB_LLVM (Ctxt.Valuation.ofHVector (lh_llvm x3 x4)) = some x →
   x = SUB_RV64 (Ctxt.Valuation.ofHVector (lh_riscv x3 x4)) := by
  unfold SUB_RV64 lh_riscv SUB_LLVM lh_llvm
  simp_alive_meta
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.sub, LLVM.sub?]
  unfold RV64.RTYPE_pure64_RISCV_SUB
  simp [HVector.cons_get_zero]
  intro h
  injection h with h₁
  rw [← h₁]

/-
@ here we model the case where nuw and nsw are set to true :
 if still no overflow return some subtraction value that is correct
 if it overflows the semantics in our dialect returns none modelling the poison value
def SUB_LLVM_flags :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add %Y, %X : i64
      llvm.return %v1 : i64
  }].denote
-/

-- true and false case
def SDIV_LLVM:=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.sdiv %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

def DIV_RV64 :=
  [RV64_com| {
  ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.div" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }].denote

theorem translation_div (x3 x4: BitVec 64) :
    SDIV_LLVM (Ctxt.Valuation.ofHVector (lh_llvm x3 x4)) = some x →
   x = DIV_RV64 (Ctxt.Valuation.ofHVector (lh_riscv x3 x4)) := by
  unfold DIV_RV64 lh_riscv SDIV_LLVM lh_llvm
  simp_alive_meta
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.sdiv, LLVM.sdiv?]
  unfold RV64.DIV_pure64_signed
  simp [HVector.cons_get_zero]
  intro h
  split at h
  · contradiction
  . simp at h


-- true and false case
def UDIV_LLVM_:=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.udiv %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

def UDIV_RV64 :=
  [RV64_com| {
  ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.divu" (%X, %Y) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }].denote


-- generate any bit vector context for the llvm and riscv
-- then we can use the translation functions to check if the translation is correct
-- we can also use the translation functions to generate the riscv code from the llvm code
def lh_llvm1 (reg: BitVec 64) : (HVector TyDenote.toType [InstCombine.Ty.bitvec 64]) :=
          HVector.cons (some (reg)) .nil

def lh_riscv1 (reg: BitVec 64)  : HVector TyDenote.toType [toRISCV.Ty.bv] :=
  HVector.cons (reg) .nil

-- to do : generalize to any context lenght
--theorem h:
   --([toRISCV.Ty.bv]).Valuation = ([InstCombine.Ty.bitvec 64]).Valuation := by sorry
--theorem map_single_context :
  --(Ctxt.Valuation.ofHVector (lh_llvm1 x))  = (Ctxt.Valuation.ofHVector (lh_riscv1 x)) := by sorry

def neg_LLVM:=
  [llvm(64)| {
^bb0(%X : i64):
      %v1 = llvm.neg  %X : i64
      llvm.return %v1 : i64
  }]
def neg_RV64 :=
 [RV64_com| {
  ^entry (%X: !i64): -- 0 10
    %c ="RV64.const" () { val = 0 : !i64 } : ( !i64) -> (!i64)
    %v1 = "RV64.sub"  (%X, %c) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64 ) -> ()
}]

theorem translate_neg(x3: BitVec 64) :
  neg_LLVM.denote (Ctxt.Valuation.ofHVector (lh_llvm1 x3)) = some x →
   x = neg_RV64.denote (Ctxt.Valuation.ofHVector (lh_riscv1 x3)) := by
  unfold neg_RV64 neg_LLVM lh_llvm1 lh_riscv1
  simp_alive_meta
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.neg, LLVM.neg? ]
  unfold RV64.RTYPE_pure64_RISCV_SUB RV64.const_func
  simp [HVector.cons_get_zero]
  intro h
  injection h with h₁
  rw [← h₁]

def not_LLVM_:=
  [llvm(64)| {
^bb0(%X : i64):
      %v1 = llvm.not %X : i64
      llvm.return %v1 : i64
  }]
def not_RV64 :=
 [RV64_com| {
  ^entry (%X: !i64):
    %c ="RV64.const" () { val = -1 : !i64 } : (!i64) -> (!i64)
    %v1 = "RV64.xor"  (%X, %c) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64 ) -> ()
}]
theorem translate_not(x3: BitVec 64) :
  not_LLVM_.denote (Ctxt.Valuation.ofHVector (lh_llvm1 x3)) = some x →
   x = not_RV64.denote (Ctxt.Valuation.ofHVector (lh_riscv1 x3)) := by
  unfold not_RV64 not_LLVM_ lh_llvm1 lh_riscv1
  simp_alive_meta
  simp_peephole [InstCombine.Op.denote,HVector.get,HVector.get, LLVM.not, LLVM.not? ]
  unfold RV64.RTYPE_pure64_RISCV_XOR RV64.const_func
  simp [HVector.cons_get_zero]
  intro h
  injection h with h₁
  rw [← h₁]
  bv_decide -- proves the fixed width bit vector arithmetic

-- to do because left out for the moment, unclear semantics
def copy_LLVM_:=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.sdiv %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

-- unclear how this matches the assembly level semantics of riscv
def trunc_LLVM_:=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.sdiv %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

-- how does LLVM use that isnt all i64 in llvm ?
def zext_LLVM_:=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.sdiv %Y, %X : i64
      llvm.return %v1 : i64
  }].denote

-- UNSURE HOW TO HANDLE THIS
  def sext_LLVM_:=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.sdiv %Y, %X : i64
      llvm.return %v1 : i64
  }].denote
