import SSA.Core.MLIRSyntax.EDSL
import SSA.Core.Framework
import SSA.Core.Util
import SSA.Core.Util.ConcreteOrMVar
import SSA.Projects.InstCombine.ForStd
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.Tactic
open LLVM

/-!
## LLVM_RISCV hybrid dialect

This file is the old version of the LLVM_RISCV dialect. The newer hybrid version of the dialect is the LLVMPlusRiscV dialect.
This file modells a llvm/riscv hybrid dialect that supports `RISC-V` instructions of type
`BitVec64` and `LLVM IR` operations of the `Option BitVec _`.

TO DO:
  parsing of the flags (disjoint, exact and overflow), couldn't figure it out properly.
  analyze how the semantics actually map between eachother.
  implement pretty printing for the dialect
  implemnt reverse printer
-/

namespace riscv.semantics

def RTYPE_pure64_RISCV_ADD (rs2_val : BitVec 64) (rs1_val : BitVec 64) :BitVec 64 :=
      BitVec.add rs1_val rs2_val

def RTYPE_pure64_RISCV_SUB (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
    BitVec.sub rs1_val rs2_val

def RTYPE_pure64_RISCV_AND (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
      BitVec.and rs2_val rs1_val

def RTYPE_pure64_RISCV_XOR(rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
      BitVec.xor rs2_val rs1_val

def RTYPE_pure64_RISCV_OR(rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
      BitVec.or rs2_val rs1_val

def RTYPE_pure64_RISCV_SLL (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
       let shamt := (BitVec.extractLsb 5 0 rs2_val).toNat;
       BitVec.shiftLeft rs1_val shamt

def RTYPE_pure64_RISCV_SRL (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
      let shamt := (BitVec.extractLsb 5 0 rs2_val).toNat;
      BitVec.ushiftRight rs1_val shamt

def RTYPE_pure64_RISCV_SRA (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
BitVec.setWidth 64
      (BitVec.extractLsb
        (63 + (BitVec.extractLsb 5 0 rs2_val).toNat)
        (BitVec.extractLsb 5 0 rs2_val).toNat
        (BitVec.signExtend
          (64 + (BitVec.extractLsb 5 0 rs2_val).toNat) rs1_val))

theorem sshiftRight_eq_setWidth_extractLsb_signExtend {w : Nat} (n : Nat) (x : BitVec w) :
    x.sshiftRight n =
    ((x.signExtend (w + n)).extractLsb (w - 1 + n) n).setWidth w := by
  ext i hi
  simp [BitVec.getElem_sshiftRight]
  simp [show i ≤ w - 1 by omega]
  simp [BitVec.getLsbD_signExtend]
  by_cases hni : (n + i) < w <;> simp [hni] <;> omega

-- TODO: @bollu says: complain to the sail→lean people to not create toNats, WTF.
theorem sshiftRight_eq_sshiftRight_extractLsb {w : Nat}
    {lw : Nat} (hlw : 2^lw = w)
    (x y : BitVec w) : x.sshiftRight y.toNat = x.sshiftRight (y.extractLsb (lw - 1) 0).toNat := by
  /-
  proof strategy:
  - show that if y has any set bits in indices [w..lw], then x.sshiftRight y = 0.
    (If y is >= w, then x.sshiftRight y = 0)
  - Otherwise, we know that y has no set bits in the range [w..lw], and therefore, y.toNat = y[0:lw].toNat
    Hence, the shift amounts have the same value.
  -/
  sorry

theorem RTYPE_pure64_RISCV_SRA_eq_sshiftRight (x y : BitVec 64) :
    RTYPE_pure64_RISCV_SRA y x = x.sshiftRight' y := by
  rw [BitVec.sshiftRight']
  rw [sshiftRight_eq_sshiftRight_extractLsb (lw := 6) (hlw := rfl)]
  rw [RTYPE_pure64_RISCV_SRA]
  rw [sshiftRight_eq_setWidth_extractLsb_signExtend]
  rfl





example (rs2_val : BitVec 64) (rs1_val : BitVec 64) :  BitVec.extractLsb' 0 64
    (BitVec.ofInt 65
      (max
        (if (9223372036854775807 < (if rs2_val.toInt = 0 then -1 else rs1_val.toInt.tdiv rs2_val.toInt)) then
          -9223372036854775808
        else (if rs2_val.toInt = 0 then -1 else rs1_val.toInt.tdiv rs2_val.toInt))
        0)) =
          BitVec.extractLsb' 0 64 (
          BitVec.ofInt 65 (if (rs2_val.toInt = 0) then 0 else (if 9223372036854775807 < (rs1_val.toInt.tdiv rs2_val.toInt) then 0 else (rs1_val.toInt.tdiv rs2_val.toInt) )  )
          )
 := by
    split
    . simp only [Int.reduceNeg, Int.reduceLT, ↓reduceIte, Int.neg_ofNat_le_ofNat, sup_of_le_right,
      BitVec.ofInt_ofNat, BitVec.extractLsb'_zero]
    . split
      . simp only [Int.reduceNeg, Int.neg_ofNat_le_ofNat, sup_of_le_right, BitVec.ofInt_ofNat,
        BitVec.extractLsb'_zero]
      . sorry


#eval 9223372036854775807  < -1

def DIV_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb' 0 64
    (BitVec.ofInt 65
      (max
        (if 9223372036854775807 < if rs2_val.toInt = 0 then -1 else rs1_val.toInt.tdiv rs2_val.toInt then
          -9223372036854775808
        else if rs2_val.toInt = 0 then -1 else rs1_val.toInt.tdiv rs2_val.toInt)
        0))

#eval DIV_pure64_signed (BitVec.ofInt 64 (-10)) (BitVec.ofInt 64 (-20))

#eval LLVM.sdiv (some (BitVec.ofInt 64 (-10))) (some (BitVec.ofInt 64 (-20)))

-- help
def DIV_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb' 0 64
    (BitVec.ofNat 65
      (if Int.ofNat rs2_val.toNat = 0 then -1 else (Int.ofNat rs1_val.toNat).tdiv (Int.ofNat rs2_val.toNat)).toNat)
-- insert the llvm add semantics

def REM_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64  :=
   BitVec.extractLsb' 0 64
    (BitVec.ofInt 65
      (Int.ofNat
        (if Int.ofNat rs2_val.toNat = 0 then Int.ofNat rs1_val.toNat
          else (Int.ofNat rs1_val.toNat).tmod (Int.ofNat rs2_val.toNat)).toNat))

def REM_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64  :=
    BitVec.extractLsb' 0 64
    (BitVec.ofInt 65
      (Int.ofNat (if rs2_val.toInt = 0 then rs1_val.toInt else rs1_val.toInt.tmod rs2_val.toInt).toNat))

def MUL_pure64_ftt (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 63 0
    (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (Int.ofNat (Int.mul rs1_val.toInt rs2_val.toInt).toNat)))

def builtin.unrealized_conversion_cast.riscvToLLVM (toCast : BitVec 64 ): Option (BitVec 64 ) := some toCast
/--
Casting a some x to x. The none (poison case) will be harded coded to zero bit vector as any
values refines a poison value.
-/
def builtin.unrealized_conversion_cast.LLVMToriscv (toCast : Option (BitVec 64)) : BitVec 64 := toCast.getD 0#64 -- rethink choice later

end riscv.semantics



namespace llvm.riscv
section Dialect


inductive Op
|riscv.add
|llvm.add (width: Nat) (nswnuw : NoWrapFlags := {nsw := false, nuw := false} ) -- defines it as an optional value and if passed overwrites the default value, else default value.
|riscv.sub
|llvm.sub (width: Nat)(nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
|llvm.not (width: Nat)
|riscv.li (val: Int)
|riscv.const  (val: Int) -- previously was const
|llvm.const (width: Nat) (val: Int)
|llvm.neg (width: Nat)
|llvm.and (width: Nat)
|riscv.and
|llvm.or (width: Nat)  (disjoint : DisjointFlag := {disjoint := false} )
|riscv.or
|llvm.xor (width: Nat)
|riscv.xor
|llvm.shl (width: Nat)  (nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
|riscv.sll
|llvm.lshr (width: Nat)(exact : ExactFlag := {exact := false} )
|riscv.srl
|riscv.sra
|llvm.ashr (width: Nat) (exact : ExactFlag := {exact := false} )
|llvm.sdiv (width: Nat) (exact : ExactFlag := {exact := false} )
|riscv.div
|llvm.udiv (width: Nat) (exact : ExactFlag := {exact := false} )
|riscv.divu
|llvm.urem (width: Nat)
|riscv.remu
|llvm.srem (width: Nat)
|riscv.rem
|llvm.mul (width: Nat)  (nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
|riscv.mul
--|riscv.li
|builtin.unrealized_conversion_cast.riscvToLLVM
|builtin.unrealized_conversion_cast.LLVMToriscv
deriving DecidableEq, Inhabited, Lean.ToExpr,Repr



inductive Ty -- here belongs what my operations operate on
  | bv : Ty -- equivalent to the type in the RISCV64 dialect.
  | bitvec : Ty -- euqivalent to the LLVM IR dialect
  -- need to add the llvm option type
  deriving DecidableEq, Repr


open TyDenote (toType) in
instance LLVMRISCVTyDenote : TyDenote Ty where
toType := fun
| Ty.bv => BitVec 64
| Ty.bitvec => Option (BitVec 64)

instance : ToString (Ty) where
  toString t := repr t |>.pretty


abbrev llvm.riscv : Dialect where
  Op := Op -- define the avaiable operations
  Ty := Ty -- define the avaiable types

@[simp, reducible] -- this basically will be the contexts
def Op.sig : Op → List Ty
|riscv.add => [Ty.bv, Ty.bv]
|llvm.add _ _ => [Ty.bitvec, Ty.bitvec] -- defines it as an optional value and if passed overwrites the default value, else default value.
|riscv.sub => [Ty.bv, Ty.bv ]
|llvm.sub _ _ => [Ty.bitvec, Ty.bitvec]
|llvm.not _ => [Ty.bitvec]
|riscv.li val => []
|riscv.const val => []
|llvm.const _ val => []
|llvm.neg _ => [Ty.bitvec]
|llvm.and _ => [Ty.bitvec, Ty.bitvec]
|riscv.and =>[Ty.bv, Ty.bv ]
|llvm.or _ _ => [Ty.bitvec, Ty.bitvec]
|riscv.or => [Ty.bv, Ty.bv ]
|llvm.xor _ => [Ty.bitvec, Ty.bitvec]
|riscv.xor => [Ty.bv, Ty.bv ]
|llvm.shl _ _ => [Ty.bitvec, Ty.bitvec]
|riscv.sll => [Ty.bv, Ty.bv ]
|llvm.lshr _ _  => [Ty.bitvec, Ty.bitvec]
|riscv.sra => [Ty.bv, Ty.bv ]
|riscv.srl => [Ty.bv, Ty.bv ]
|llvm.ashr _ _ => [Ty.bitvec, Ty.bitvec]
|llvm.sdiv _ _ => [Ty.bitvec, Ty.bitvec]
|riscv.div => [Ty.bv, Ty.bv ]
|llvm.udiv _ _ =>[Ty.bitvec, Ty.bitvec]
|riscv.divu => [Ty.bv, Ty.bv ]
|llvm.urem _  => [Ty.bitvec, Ty.bitvec]
|riscv.remu => [Ty.bv, Ty.bv]
|llvm.srem _ => [Ty.bitvec, Ty.bitvec]
|riscv.rem => [Ty.bv, Ty.bv ]
|llvm.mul _ _ => [Ty.bitvec, Ty.bitvec]
|riscv.mul => [Ty.bv, Ty.bv ]
|builtin.unrealized_conversion_cast.riscvToLLVM => [Ty.bv] --bit vector to option bit vector
|builtin.unrealized_conversion_cast.LLVMToriscv => [Ty.bitvec] -- option bit vector to concrete bit vector


@[simp, reducible] -- reduceable means this expression can always be expanded by the type checker when type checking
-- output signature , part of an op
def Op.outTy : Op  → Ty
|riscv.add => .bv
|llvm.add _ flags => .bitvec
|riscv.sub => .bv
|llvm.sub _ _ => .bitvec
|llvm.not _ => .bitvec
|riscv.li val  => .bv
|riscv.const val  => .bv
|llvm.const _ val  => .bitvec
|llvm.neg _ => .bitvec
|llvm.and _ => .bitvec
|riscv.and => .bv
|llvm.or _ _ => .bitvec
|riscv.or => .bv
|llvm.xor _ => .bitvec
|riscv.xor => .bv
|llvm.shl _ _ => .bitvec
|riscv.sll => .bv
|llvm.lshr _ _ => .bitvec
|riscv.srl => .bv
|riscv.sra => .bv
|llvm.ashr _ _ => .bitvec
|llvm.sdiv _ _ => .bitvec
|riscv.div => .bv
|llvm.udiv _ _ => .bitvec
|riscv.divu => .bv
|llvm.urem _ => .bitvec
|riscv.remu => .bv
|llvm.srem _ => .bitvec
|riscv.rem => .bv
|llvm.mul _ _ => .bitvec
|riscv.mul => .bv
|builtin.unrealized_conversion_cast.riscvToLLVM => .bitvec-- casting bit vector to option bit vector
|builtin.unrealized_conversion_cast.LLVMToriscv => .bv -- casting option bit vector to bit vector
@[simp, reducible]
def Op.signature : Op → Signature (Ty) :=
  fun o => {sig := Op.sig o, outTy := Op.outTy o, regSig := []}

instance : DialectSignature llvm.riscv := ⟨Op.signature⟩

open LLVM

@[simp, reducible] -- structure is parameter to the op, then arguemtns then return type
instance : DialectDenote (llvm.riscv) where denote
  |.riscv.add, regs, _ => riscv.semantics.RTYPE_pure64_RISCV_ADD (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.sub, regs,_  => riscv.semantics.RTYPE_pure64_RISCV_SUB (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.const val, _, _ => BitVec.ofInt 64 val
  |.riscv.li val, _, _ => BitVec.ofInt 64 val
  |.riscv.and, regs, _  => riscv.semantics.RTYPE_pure64_RISCV_AND (regs.getN 1 (by simp [DialectSignature.sig, signature])) (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.xor, regs, _  => riscv.semantics.RTYPE_pure64_RISCV_XOR (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.sll, regs, _  => riscv.semantics.RTYPE_pure64_RISCV_SLL (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.or, regs, _  => riscv.semantics.RTYPE_pure64_RISCV_OR (regs.getN 1 (by simp [DialectSignature.sig, signature])) (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.srl, regs, _  => riscv.semantics.RTYPE_pure64_RISCV_SRL (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.sra, regs, _  =>  riscv.semantics.RTYPE_pure64_RISCV_SRA (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.div, regs, _  => riscv.semantics.DIV_pure64_signed (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.divu, regs, _ => riscv.semantics.DIV_pure64_unsigned (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.remu, regs,_  =>  riscv.semantics.REM_pure64_unsigned (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.rem, regs,_ => riscv.semantics.REM_pure64_signed (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.riscv.mul, regs, _ => riscv.semantics.MUL_pure64_ftt (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.llvm.add _ flags, op, _  => LLVM.add (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flags
  |.llvm.sub _ flags,op,_ => LLVM.sub (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flags
  |.llvm.not _, op,_ => LLVM.not  (op.getN 0 (by simp [DialectSignature.sig, signature]))
  |.llvm.neg _, op,_ => LLVM.neg (op.getN 0 (by simp [DialectSignature.sig, signature]))
  |.llvm.and _, op,_ => LLVM.and  (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature]))
  |.llvm.or _ flag, op,_  => LLVM.or       (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flag
  |.llvm.xor _, op, _  => LLVM.xor (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature]))
  |.llvm.shl _ flags, op,_  => LLVM.shl      (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flags
  |.llvm.lshr _ flags, op,_  => LLVM.lshr     (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flags
  |.llvm.ashr _ flag, op,_ => LLVM.ashr     (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flag
  |.llvm.sdiv _ flag, op,_  => LLVM.sdiv     (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flag
  |.llvm.udiv _ flag, op,_ => LLVM.udiv    (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flag
  |.llvm.urem _, op, _ => LLVM.urem     (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature]))
  |.llvm.srem _, op,_  => LLVM.srem     (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature]))
  |.llvm.mul _  flags, op,_ => LLVM.mul      (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flags
  |.llvm.const _ val, _ , _ => some (BitVec.ofInt 64 val)
  |.builtin.unrealized_conversion_cast.riscvToLLVM, elemToCast, _  => riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM  (elemToCast.getN 0 (by simp [DialectSignature.sig, signature]))
  |.builtin.unrealized_conversion_cast.LLVMToriscv, elemToCast, _ => riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv (elemToCast.getN 0 (by simp [DialectSignature.sig, signature]))

/-
  |.llvm.sub _, _ => .opt64
  |.llvm.not _ => .opt64
  |.riscv.const val => BitVec.ofInt 64 val
  |.llvm.neg _ => .opt64
  |.llvm.and _ => .opt64
  |.riscv.and => RV64.RTYPE_pure64_RISCV_AND (regs.getN 0 (by simp [DialectSignature.sig, signature])) (regs.getN 1 (by simp [DialectSignature.sig, signature]))
  |.llvm.or _, _ => .opt64
  |.riscv.or  => RV64.RTYPE_pure64_RISCV_OR (regs.getN 0 (by simp [DialectSignature.sig, signature])) (regs.getN 1 (by simp [DialectSignature.sig, signature]))
  |.llvm.xor _ => .opt64
  |.riscv.xor => .bv64
  |.llvm.shl _, _ => .opt64
  |.riscv.sll => .bv64
  |.llvm.lshr _, _ => .opt64
  |.riscv.srl => .bv64
  |.riscv.ashr => .bv64
  |.llvm.ashr _ _ => .opt64
  |.llvm.sdiv _ _ => .opt64
  |.riscv.div => .bv64
  |.llvm.udiv _ _ => .opt64
  |.riscv.divu => .bv64
  |.llvm.urem _ => .opt64
  |.riscv.remu => .bv64
  |.llvm.srem _ => .opt64
  |.riscv.rem => .bv64
  |.llvm.mul _, _ => .opt64
  |.riscv.mul => .bv64
-/
end Dialect

-- helper functions to easier create expressions and check the parsing of a program writtin in IR style into Com and Expr.
def riscv.add {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bv) : Expr llvm.riscv Γ .pure .bv  :=
  Expr.mk
    (op := llvm.riscv.Op.riscv.add)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def llvm.add {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bitvec) : Expr llvm.riscv Γ .pure .bitvec  :=
  Expr.mk
    (op := llvm.riscv.Op.llvm.add 64)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def riscv.sub {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bv) : Expr llvm.riscv Γ .pure .bv  :=
  Expr.mk
    (op := llvm.riscv.Op.riscv.sub)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def llvm.sub {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bitvec) : Expr llvm.riscv Γ .pure .bitvec  :=
  Expr.mk
    (op := llvm.riscv.Op.llvm.sub 64)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def llvm.not {Γ : Ctxt _} (e₁: Ctxt.Var Γ .bitvec) : Expr llvm.riscv Γ .pure .bitvec  :=
    Expr.mk
    (op := llvm.riscv.Op.llvm.not 64)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .nil)
    (regArgs := HVector.nil)

def llvm.neg {Γ : Ctxt _} (e₁: Ctxt.Var Γ .bitvec) : Expr llvm.riscv Γ .pure .bitvec  :=
    Expr.mk
    (op := llvm.riscv.Op.llvm.neg 64)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .nil)
    (regArgs := HVector.nil)

def llvm.and {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bitvec) : Expr llvm.riscv Γ .pure .bitvec  :=
  Expr.mk
    (op := llvm.riscv.Op.llvm.and 64)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def llvm.or {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bitvec) : Expr llvm.riscv Γ .pure .bitvec  :=
  Expr.mk
    (op := llvm.riscv.Op.llvm.or 64)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def llvm.xor {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bitvec) : Expr llvm.riscv Γ .pure .bitvec  :=
  Expr.mk
    (op := llvm.riscv.Op.llvm.xor 64)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def riscv.mul {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bv) : Expr llvm.riscv Γ .pure .bv  :=
  Expr.mk
    (op := llvm.riscv.Op.riscv.mul)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def llvm.mul {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bitvec) : Expr llvm.riscv Γ .pure .bitvec  :=
  Expr.mk
    (op := llvm.riscv.Op.llvm.mul 64)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def riscv.const {Γ : Ctxt _} (n : ℤ) : Expr llvm.riscv Γ .pure .bv  :=
  Expr.mk
    (op := llvm.riscv.Op.riscv.const n)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := HVector.nil)

def llvm.const {Γ : Ctxt _} (n : ℤ) : Expr llvm.riscv Γ .pure .bitvec  :=
  Expr.mk
    (op := llvm.riscv.Op.llvm.const 64 n)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := HVector.nil)


/-
def riscv.const {Γ : Ctxt _} (n : ℤ) : Expr llvm.riscv Γ .pure .bv64  :=
  Expr.mk
    (op := llvm.riscv.Op.riscv.const n)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := HVector.nil)

def llvm.const {Γ : Ctxt _} (n : ℤ) : Expr llvm.riscv Γ .pure .opt64  :=
  Expr.mk
    (op := llvm.riscv.Op.llvm.const 64 n)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := HVector.nil)

-/
def mkTy : MLIR.AST.MLIRType φ → MLIR.AST.ExceptM llvm.riscv llvm.riscv.Ty
  | MLIR.AST.MLIRType.undefined s => do
    match s with
    | "r64" => return .bv --maybe change it later
    | "riscv.reg" => return .bv -- to make it compatible with the MLIR representation of riscv.
    | "i64" => return .bitvec
    | _ => throw .unsupportedType
  | _ => throw .unsupportedType

instance instTransformTy : MLIR.AST.TransformTy llvm.riscv 0 where
  mkTy := mkTy

/-
  |.builtin.unrealized_conversion_cast.riscvToLLVM, elemToCast, _  => riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM  (elemToCast.getN 0 (by simp [DialectSignature.sig, signature]))
  |.builtin.unrealized_conversion_cast.LLVMToriscv, elemToCast,

  def mkExpr (Γ : Ctxt _) (opStx : MLIR.AST.Op 0) :
  MLIR.AST.ReaderM (llvm.riscv) (Σ eff ty, Expr (llvm.riscv) Γ eff ty) := do
    match mkExpr with -- use the llvm parser else use the riscv parser



-/
-- idea have a type that is either llvm type or riscv type
-- implement staged parsing --> llvm to riscv



def mkExpr (Γ : Ctxt _) (opStx : MLIR.AST.Op 0) :
  MLIR.AST.ReaderM (llvm.riscv) (Σ eff ty, Expr (llvm.riscv) Γ eff ty) := do
    match opStx.args with
    | []  => do
        let some att := opStx.attrs.getAttr "val"
          | throw <| .unsupportedOp s!"no attirbute in const {repr opStx}"
        match att, opStx.name with
          | .int val ty, "riscv.li" =>
            let opTy← mkTy ty -- ty.mkTy
            match h: opTy with
            | .bv =>
              return ⟨.pure, opTy, ⟨
                .riscv.li (val), -- needed to add this extra mechanism in parsing
                by
                simp[DialectSignature.outTy, signature, h]
              ,
                by constructor,
                .nil,
                .nil
              ⟩⟩
            | _ =>  throw <| .unsupportedOp s!"unsupported operation: tried to input an Option BitVec to riscv.li {repr opStx}"
          | _, _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
    | v₁Stx :: [] =>
       let ⟨ty₁, v₁⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₁Stx
       match ty₁, opStx.name with
       | .bitvec , "llvm.neg"=> -- unsure if handeld flags correctly
              return ⟨ .pure, .bitvec ,⟨.llvm.neg 64 , by rfl, by constructor,
               .cons v₁ <| .nil,
                .nil⟩⟩
       | .bitvec , "llvm.not"=> -- unsure if handeld flags correctly
              return ⟨ .pure, .bitvec ,⟨ .llvm.not 64 , by rfl, by constructor,
               .cons v₁ <| .nil,
                .nil⟩⟩
        | .bv , "builtin.unrealized_conversion_cast.riscvToLLVM"=>
              return ⟨ .pure, .bitvec ,⟨ .builtin.unrealized_conversion_cast.riscvToLLVM , by rfl, by constructor,
               .cons v₁ <| .nil,
                .nil⟩⟩
        | .bitvec , "builtin.unrealized_conversion_cast.LLVMToriscv"=>
              return ⟨ .pure, .bv ,⟨ .builtin.unrealized_conversion_cast.LLVMToriscv , by rfl, by constructor,
               .cons v₁ <| .nil,
                .nil⟩⟩
        | .bitvec , "llvm.const"=> -- unsure if handeld flags correctly
            let some att := opStx.attrs.getAttr "val"
              | throw <| .unsupportedOp s!"no attirbute in constant value provided {repr opStx}"
              match att with
              | .int val ty => -- ides modell it as a list of 3 bools
                --let opTy@(.opt64) ← mkTy ty -- ty.mkTy -- potential debug
                return ⟨.pure, .bitvec, ⟨
                  .llvm.const 64 val,
                  by
                  simp[DialectSignature.outTy, signature]
                ,
                  by constructor,
                  .nil,
                  .nil
                ⟩⟩
              | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"

       | _ ,_=> throw <| .unsupportedOp s!"is a one argument op but shouldnt be one, cant find a matching case  {repr opStx}"
    | v₁Stx::v₂Stx:: [] =>
        let ⟨ty₁, v₁⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₁Stx
        let ⟨ty₂, v₂⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₂Stx
        match ty₁, ty₂, opStx.name with
        | .bv , .bv , "riscv.add" => --refers to an assembly add
              return ⟨ .pure, .bv ,⟨ .riscv.add, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "riscv.sub" =>
              return ⟨ .pure, .bv ,⟨ .riscv.sub, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "riscv.and" =>
              return ⟨ .pure, .bv ,⟨ .riscv.and, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "riscv.xor" =>
              return ⟨ .pure, .bv ,⟨ .riscv.xor, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv, .bv , "riscv.sll" =>
              return ⟨ .pure, .bv ,⟨ .riscv.sll, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "riscv.or" =>
              return ⟨ .pure, .bv ,⟨ .riscv.or, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "riscv.srl" =>
              return ⟨ .pure, .bv ,⟨ .riscv.srl, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "riscv.sra" =>
              return ⟨ .pure, .bv ,⟨ .riscv.sra, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv, .bv , "riscv.div" =>
              return ⟨ .pure, .bv ,⟨ .riscv.div, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "riscv.divu" =>
              return ⟨ .pure, .bv ,⟨ .riscv.divu, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "riscv.remu" =>
              return ⟨ .pure, .bv ,⟨ .riscv.remu, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "riscv.rem" =>
              return ⟨ .pure, .bv ,⟨ .riscv.rem, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "riscv.mul" =>
              return ⟨ .pure, .bv ,⟨ .riscv.mul, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bitvec , .bitvec , "llvm.add" => -- unsure if handeld flags correctly

              return ⟨ .pure, .bitvec ,⟨ .llvm.add 64 , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bitvec ,.bitvec , "llvm.sub" => -- unsure if handeld flags correctly
              return ⟨ .pure, .bitvec ,⟨ .llvm.sub 64 , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bitvec , .bitvec , "llvm.and" => -- unsure if handeld flags correctly
              return ⟨ .pure, .bitvec ,⟨ .llvm.and 64 , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
          -- TO DO handle the attributes
          /-
          add, sub, or, shl, lshr, ashr, sdiv, udiv, mul have flags
          -/
        | .bitvec , .bitvec , "llvm.or" => do -- unsure if handeld flags correctly, flags are wrong atm
            let att := opStx.attrs.getAttr "disjoint"
                return ⟨.pure, .bitvec, ⟨
                  .llvm.or 64 ⟨att.isSome⟩,
                  by
                  simp[DialectSignature.outTy, signature]
                ,
                  by constructor,
                  .cons v₁ <| .cons v₂ <| .nil,
                  .nil
                ⟩⟩
        | .bitvec , .bitvec , "llvm.xor" => -- unsure if handeld flags correctly
              return ⟨ .pure, .bitvec ,⟨ .llvm.xor 64 , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bitvec , .bitvec , "llvm.lshr" => do -- unsure if handeld flags correctly
              let exactFlag := opStx.attrs.getAttr "exact"
              return ⟨ .pure, .bitvec ,⟨ .llvm.lshr 64 ⟨exactFlag.isSome⟩ , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bitvec ,.bitvec , "llvm.ashr" => do -- unsure if handeld flags correctly
          let exactFlag := opStx.attrs.getAttr "exact"
              return ⟨ .pure, .bitvec,⟨ .llvm.ashr 64 ⟨exactFlag.isSome⟩ , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bitvec , .bitvec , "llvm.sdiv" => do -- unsure if handeld flags correctly
              let exactFlag := opStx.attrs.getAttr "exact"
              return ⟨ .pure, .bitvec ,⟨ .llvm.sdiv 64 ⟨exactFlag.isSome⟩ , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bitvec , .bitvec , "llvm.udiv" => do -- unsure if handeld flags correctly
              let exactFlag := opStx.attrs.getAttr "exact"
              return ⟨ .pure, .bitvec ,⟨ .llvm.udiv 64 ⟨exactFlag.isSome⟩, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bitvec , .bitvec, "llvm.shl" => do -- unsure if handeld flags correctly
              return ⟨ .pure, .bitvec ,⟨ .llvm.shl 64 , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bitvec , .bitvec , "llvm.srem" => -- unsure if handeld flags correctly
              return ⟨ .pure, .bitvec ,⟨ .llvm.srem 64 , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bitvec , .bitvec , "llvm.urem" => -- unsure if handeld flags correctly
              return ⟨ .pure,.bitvec ,⟨ .llvm.urem 64 , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bitvec , .bitvec , "llvm.mul" =>
              return ⟨ .pure, .bitvec ,⟨ .llvm.mul 64   , by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | _ ,_, _ => throw <| .unsupportedOp s!"wrong number of arguemnts, more than 2 arguemnts  {repr opStx}"
    | _  => throw <| .unsupportedOp "didnt implement instruction yet "


instance : MLIR.AST.TransformExpr (llvm.riscv) 0 where
  mkExpr := mkExpr

def mkReturn (Γ : Ctxt _) (opStx : MLIR.AST.Op 0) : MLIR.AST.ReaderM (llvm.riscv)
    (Σ eff ty, Com llvm.riscv Γ eff ty) :=
  if opStx.name == "return"
  then match opStx.args with
  | vStx::[] => do
    let ⟨ty, v⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ vStx
    return ⟨.pure, ty, Com.ret v⟩
  | _ => throw <| .generic s!"Ill-formed return statement (wrong arity, expected 1, got {opStx.args.length})"
  else throw <| .generic s!"Tried to build return out of non-return statement {opStx.name}"

instance : MLIR.AST.TransformReturn (llvm.riscv) 0 where
  mkReturn := mkReturn

open Qq MLIR AST Lean Elab Term Meta in
elab "[_| " reg:mlir_region "]" : term => do
  SSA.elabIntoCom reg q(llvm.riscv)

end llvm.riscv

open LLVM
open llvm.riscv

/- instead of lowering implemented by myself implement a lowering using the peephole rewriter and extend the rewriter to
work with refinements
-/

def exampleLLVM  :=
[_|{
  ^entry (%0: !i64 ):
  %1 = "llvm.add" (%0, %0)  : (!i64, !i64 ) -> (!i64)
  "return" (%1) : ( !i64) -> ()
}]

def exampleLLVMOr  :=
[_|{
  ^entry (%0: !i64 ):
  %1 = "llvm.or" (%0, %0) { } : (!i64, !i64 ) -> (!i64)
  "return" (%1) : ( !i64) -> ()
}]
def exampleRiscv : Com llvm.riscv [.bv] .pure .bv :=
[_| {
  ^entry (%0: !r64 ):
  %1 = "riscv.add" (%0, %0) : (!r64, !r64 ) -> (!r64)
  "return" (%1) : ( !r64) -> ()
}]


 def LLVMCtxtToRV (Γ : Ctxt llvm.riscv.Ty) : Ctxt llvm.riscv.Ty :=
  List.replicate Γ.length (.bv)

/--TO DO: ask for a shorter proof.-/

def LLVMVarToRV : Γ.Var (.bitvec) → (LLVMCtxtToRV Γ).Var .bv
  | ⟨i, h⟩ =>  ⟨i, by
  simp [LLVMCtxtToRV]
  have hcontra2 : Γ.get? i = some (.bitvec) := by exact h
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
  simp
  ⟩


-- function that rewrites ahn expression into a computation
variable {d} [DialectSignature d]
def Com.ofExpr : Expr d Γ eff t → Com d Γ eff t := fun e =>
  Com.var e <| Com.ret <| Ctxt.Var.last _ _



-- do I need to establish a context mapping or exetend the context Γ
def lowerSimpleIRInstructionDialect (e : Expr llvm.riscv Γ .pure .bitvec) :  Expr llvm.riscv (LLVMCtxtToRV Γ) .pure .bv :=
  match e with
  | Expr.mk
    (.llvm.add 64 flags)
    (_)
    (_)
    (.cons e₁ <| .cons e₂ <| .nil ) -- are of type .opt64 which are option bitvector -> can either extract them and add them to the context but then need to know
    (_) =>  Expr.mk
    (op := .riscv.add)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons  (LLVMVarToRV e₁) <| .cons  (LLVMVarToRV e₂) <| .nil  )
    (regArgs := .nil)
  |e  =>
    Expr.mk
    (op := .riscv.const 0) -- for the moment hard coded to zero.
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args :=  .nil  )
    (regArgs := .nil)

    -- still wrong type
def loweringLLVMtoRISCV : {Γ : Ctxt llvm.riscv.Ty} → (com : Com llvm.riscv Γ .pure (.bitvec)) → Option (Com llvm.riscv (LLVMCtxtToRV Γ)  .pure (.bv))
  | _, Com.ret x  =>  some (Com.ret (LLVMVarToRV x))
  | _, Com.var (α := llvm.riscv.Ty.bitvec) e c' =>
        let e' := (lowerSimpleIRInstructionDialect e) -- map the expression to a riscv expression
        match loweringLLVMtoRISCV c' with
        | some com => some (Com.var (e') (com))
        | none => none
  | _, Com.var (α := llvm.riscv.Ty.bv) e1 e2 => none --, shoulnt call the lowering on itself some (Com.var (α := llvm.riscv.Ty.bv64) e1 e2) ---


/-
def LLVMCtxtToRVInHybrid  (Γ : Ctxt llvm.riscv.Ty) : Ctxt llvm.riscv.Ty :=
  List.replicate Γ.length (.bv)

def LLVMValuationToRV {Γ : Ctxt llvm.riscv.Ty} (V : Γ.Valuation) : (LLVMCtxtToRV Γ).Valuation :=
  fun t v => -- A valuation is a function that takes in a type and variable (index and proof that it has the correspondig type) and returns an value of the correct type.
    match t with
    | .bv =>
      let i : Fin Γ.length := ⟨v.1, by -- extract information from the llvm variable
          simpa [LLVMCtxtToRV, List.getElem?_eq_some_iff ] using v.prop
       ⟩ -- this is a simplification for simp [...] at using h where we defined h to be v.prop
      match h : Γ.get i with -- trick to get a let binding into the list of things we know.
      | Ty.bitvec w =>
           let (v' : Γ.Var (Ty.bitvec w)) := ⟨v.1, by
              simpa [List.getElem?_eq_some_iff,i, i.prop] using h
        ⟩
        (V v' : LLVM.IntW w).getD 0#_ |>.setWidth 64

-/


/-
-- need to restrict to to only llvm context vs only riscv context
theorem lowerSimpleIRInstruction_correct
    (e : Expr llvm.riscv Γ .pure (.bitvec)) (V : Γ.Valuation) :
    ∀ x, (e.denote V) = some x → (lowerSimpleIRInstructionDialect e).denote (LLVMValuationToRV V) = x := by
  intros x h1
  rcases e with ⟨op1, ty_eq1, eff_le1,args1, regionArgs1⟩
  case mk =>
    cases op1
    case unary w op =>
      cases op
      /- case neg => sorry
      case not => sorry
      case copy => sorry
      case trunc => sorry
      case zext => sorry
      case sext => sorry-/
    case binary w op =>
      cases op
      case and =>
        simp at ty_eq1
        unfold DialectSignature.outTy at ty_eq1
        simp at ty_eq1
        simp [signature] at ty_eq1
        subst ty_eq1
        simp [lowerSimpleIRInstruction]
        unfold DialectSignature.sig at args1
        simp at args1
        simp only [signature, InstCombine.MOp.sig,InstCombine.MOp.outTy] at args1
        unfold DialectSignature.effectKind at eff_le1
        simp at eff_le1
        simp only [signature] at eff_le1
        -- simp_peephole at h1 when apply these the whole hyptohesis h vanishes
        simp_peephole
        simp


-/
/--
## Example Section
TO DO: implement pretty printing for it
-/
-- unrealized_conversion_cast examples
def unrealized_conversion_cast_testRiscvToLLVM :  Com llvm.riscv (Ctxt.ofList [.bv]) .pure .bitvec:=
  [_| {
    ^entry (%0: !r64 ):
    %1 = "builtin.unrealized_conversion_cast.riscvToLLVM" (%0) : (!r64) -> (!i64)
    "return" (%1) : (!i64) -> ()
  }]

def unrealized_conversion_cast.LLVMToriscv :  Com llvm.riscv (Ctxt.ofList [.bitvec]) .pure .bv :=
  [_| {
    ^entry (%0: !i64 ):
    %1 = "builtin.unrealized_conversion_cast.LLVMToriscv" (%0) : (!i64) -> (!r64)
    "return" (%1) : (!r64) -> ()
  }]

def exampleLLVM1 : Com llvm.riscv (Ctxt.ofList [.bitvec]) .pure .bitvec :=
[_|{
  ^entry (%0: !i64 ):
  %1 = "llvm.add" (%0, %0) : (!i64, !i64 ) -> (!i64)
  "return" (%1) : ( !i64) -> ()
}]
#eval loweringLLVMtoRISCV (exampleLLVM1)

def exampleRiscv1 : Com llvm.riscv (Ctxt.ofList [.bv]) .pure .bv :=
[_| {
  ^entry (%0: !r64 ):
  %1 = "riscv.add" (%0, %0) : (!r64, !r64 ) -> (!r64)
  "return" (%1) : ( !r64) -> ()
}]
def exampleRiscv1PRETTY  : Com llvm.riscv (Ctxt.ofList [.bv]) .pure .bv :=
[_| {
  ^entry (%0: !r64 ):
  %1 = "riscv.add" (%0, %0) : (!r64, !r64 ) -> (!r64)
  "return" (%1) : ( !r64) -> ()
}]








/-
  %addi32 = arith.addi %lhsi32, %rhsi32 : i32
}

(venv) sarahkuhn@Sarahs-MacBook-Pro-2 xdsl-experiments % xdsl-opt add.mlir -p convert-arith-to-riscv
builtin.module {
  %addi32 = builtin.unrealized_conversion_cast %lhsi32_1 : i32 to !riscv.reg
  %addi32_1 = builtin.unrealized_conversion_cast %rhsi32_1 : i32 to !riscv.reg
  %addi32_2 = riscv.add %addi32, %addi32_1 : (!riscv.reg, !riscv.reg) -> !riscv.reg
  %addi32_3 = builtin.unrealized_conversion_cast %addi32_2 : !riscv.reg to i32
-/

/--
  |.builtin.unrealized_conversion_cast.riscvToLLVM, elemToCast, _  => riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM  (elemToCast.getN 0 (by simp [DialectSignature.sig, signature]))
  |.builtin.unrealized_conversion_cast.LLVMToriscv, elemToCast, _ =>
-/

-- test if the intra dialect lowering works
def testAddLowering : loweringLLVMtoRISCV exampleLLVM1 = some (exampleRiscv1) := by native_decide
/-
 rhs:=
[_| {
  ^entry (%0: !r64 ):
  %1 = "add" (%0, %0) : (!r64, !r64 ) -> (!r64)
  "return" (%1) : ( !r64) -> ()
}], correct := by sorry }

-/
