
import RiscvDialect.RISCV64.Semantics
import SSA.Core.Framework
import RiscvDialect.RISCV64.removeToIntToNat
set_option maxHeartbeats 1000000000000000000

open RV64Semantics /- access the semantics -/

namespace RISCV64
/-! ## The `RISCV64` dialect -/

/-!
## Dialect operation definitions
Modelled operations such that their inputs arguments are up to two register content values. Any other attributes e.g flags
are encoded as part of the op-code.

We modell the RV64I base instruction set: https://github.com/riscv/riscv-isa-manual/blob/main/src/rv64.adoc, therefore allow for an 64-bit address space.
And operations out of selected RISC-V extension:
    - `M`: standart integer division and multiplication instruction extension

    - `B`: extension for bit manipulation (comprises instructions provided by the `Zba`, `Zbb`, and `Zbs` extensions)
            here: https://github.com/riscv/riscv-isa-manual/blob/main/src/b-st-ext.adoc

    - `Zicond` : extension for conditional operations https://github.com/riscvarchive/riscv-zicond/blob/main/zicondops.adoc
-/
set_option maxHeartbeats 1000000 in -- we need this because .... to do
inductive Op
|  li : (val : Int) → Op
|  lui (imm : BitVec 20)
|  auipc (imm : BitVec 20)
|  addi (imm : BitVec 12)
|  andi (imm : BitVec 12)
|  ori (imm : BitVec 12)
|  xori (imm : BitVec 12)
|  addiw (imm : BitVec 12)
|  add
|  slli (shamt : BitVec 6)
|  sub
|  and
|  or
|  xor
|  sll
|  srl
|  sra
|  addw
|  subw
|  sllw
|  srlw
|  sraw
-- fence
|  slti (imm : BitVec 12)
|  sltiu (imm : BitVec 12)
|  srli (shamt : BitVec 6)
|  srai (shamt : BitVec 6)
|  slliw (shamt : BitVec 5)
|  srliw (shamt : BitVec 5)
|  sraiw (shamt : BitVec 5)
|  slt
|  sltu
-- RISC-V `M` extension instructions (multiply& divide)
| mul    -- performs signed multiplication on 64 x 64 bits and returns the lower 64 bits of the result .
| mulu   -- performs unsigned multiplication on 64 x 64 bits and returns the lower 64 bits of the result .
| mulw
| mulh   -- performs signed multiplication on 64 x 64 bits and returns the upper 64 bits of the result.
| mulhu  -- performs unsigned multiplication on 64 x 64 bits and returns the upper 64 bits of the result.
| mulhsu -- performs multiplication on (rs1 signed) x (rs2 unsigned) and returns the upper 64 bits of the result.
| divw
| divwu
| div    -- signed division
| divu   -- unsigned division
| remw
| rem    --sign of result is according to sign of dividend
| remwu
| remu
-- RISC-V `Zba` extension
| add.uw
| sh1add.uw
| sh2add.uw
| sh3add.uw
| sh1add
| sh2add
| sh3add
-- slli.uw missing
-- part of the RISC-V `Zbb` & `Zbkb` extension
| rol
| ror
| rolw
| rorw
| sext.b
| sext.h
| zext.h
/-
|pack
|packh
-/
-- part of the RISC-V `Zbs` extension
| bclr
| bclri (shamt : BitVec 6)
| bext
| bexti (shamt : BitVec 6)
| binv
| binvi (shamt : BitVec 6)
| bset
| bseti (shamt : BitVec 6)
/- RISC-V `Zicond` conditional operations extension  -/
| czero.eqz
| czero.nez
deriving DecidableEq



instance : Repr (Op) where
  reprPrec
    | .bext , _ => "bext"
    | .add , _ => "add"
    | _ , _ => "const"


#eval repr Op.bext
/-
TO DO in the future: zbb_rytpe full -> will be implementeed as soon as MVP exists.
| andn
| orn
| xnor
| max
| maxu
| min
| minu
| rol --> done
| ror --> done
-/


/--
## Dialect type definitions
Defining a type system for the `RISCV64` dialect. `bv` represents bit vector.
-/
inductive Ty
  | bv : Ty
  deriving DecidableEq, Inhabited

instance : Repr (Ty) where
  reprPrec
    | .bv, _ => "reg64" -- wildcard is for predcedence level


#eval repr Ty.bv

/-

def reprForRiscvAsm (op : _ ) : Format :=
  let out : String := match op with
    | _ => "add"
  Repr.addAppParen (Format.group (Format.nest
    (if prec >= max_prec then 1 else 2) f!"llvm.{op}"))
    prec -/

instance : ToString (Ty) where
  toString t := repr t |>.pretty



/-!
Connecting the `bv` type to its underlying Lean type `BitVec 64`. By providing a `TyDenote` instance,
we define how the `RISCV64` types transalte into actual Lean types.
-/
instance : TyDenote Ty where
toType := fun
| Ty.bv => BitVec 64

instance (ty : Ty) : Inhabited (TyDenote.toType ty) where
  default := match ty with
    | .bv  => 0#64

/--
## Dialect operation definitions

Specifing the signature of each `RISCV64` operation. `Sig` refers to the input types
for each operation as a list of types.

We mark it as `simp` and `reducible` such that the type checker and elaborator
always fully unfold a `sig` to its underlying defintion and when the simplifier
encounters a `sig` it can replace it by its definition.
-/

@[simp, reducible]
def Op.sig : Op → List Ty
  | .li _ => []
  | .mulu  => [Ty.bv, Ty.bv]
  | .mulh  => [Ty.bv, Ty.bv]
  | .mulhu  => [Ty.bv, Ty.bv]
  | .mulhsu  => [Ty.bv, Ty.bv]
  | .divu =>  [Ty.bv, Ty.bv]
  | .rol => [Ty.bv, Ty.bv]
  | .ror => [Ty.bv, Ty.bv]
  | .remwu  => [Ty.bv, Ty.bv]
  | .remu  =>  [Ty.bv, Ty.bv]
  | .addiw (imm : BitVec 12) => [Ty.bv]
  | .lui (imm : BitVec 20) => [Ty.bv]
  | .auipc (imm : BitVec 20)  => [Ty.bv]
  | .slliw (shamt : BitVec 5)  => [Ty.bv]
  | .srliw (shamt : BitVec 5) => [Ty.bv]
  | .sraiw (shamt : BitVec 5) => [Ty.bv]
  | .slli (shamt : BitVec 6) => [Ty.bv]
  | .srli (shamt : BitVec 6) => [Ty.bv]
  | .srai (shamt : BitVec 6) => [Ty.bv]
  | .addw => [Ty.bv, Ty.bv]
  | .subw => [Ty.bv, Ty.bv]
  | .sllw => [Ty.bv, Ty.bv]
  | .srlw => [Ty.bv, Ty.bv]
  | .sraw => [Ty.bv, Ty.bv]
  | .add => [Ty.bv, Ty.bv]
  | .slt => [Ty.bv, Ty.bv]
  | .sltu => [Ty.bv, Ty.bv]
  | .and => [Ty.bv, Ty.bv]
  | .or => [Ty.bv, Ty.bv]
  | .xor => [Ty.bv, Ty.bv]
  | .sll => [Ty.bv, Ty.bv]
  | .srl => [Ty.bv, Ty.bv]
  | .sub => [Ty.bv, Ty.bv]
  | .sra => [Ty.bv, Ty.bv]
  | .remw  => [Ty.bv, Ty.bv]
  | .rem  =>  [Ty.bv, Ty.bv]
  | .mul => [Ty.bv, Ty.bv]
  | .mulw => [Ty.bv, Ty.bv]
  | .div  =>  [Ty.bv, Ty.bv]
  | .divw  =>  [Ty.bv, Ty.bv]
  | .divwu  =>  [Ty.bv, Ty.bv]
  | .addi (imm : BitVec 12) => [Ty.bv]
  | .slti (imm : BitVec 12) => [Ty.bv]
  | .sltiu (imm : BitVec 12) => [Ty.bv]
  | .andi (imm : BitVec 12) => [Ty.bv]
  | .ori (imm : BitVec 12) => [Ty.bv]
  | .xori (imm : BitVec 12) => [Ty.bv]
  | .czero.eqz =>  [Ty.bv, Ty.bv]
  | .czero.nez =>  [Ty.bv, Ty.bv]
  | .sext.b => [Ty.bv]
  | .sext.h => [Ty.bv]
  | .zext.h => [Ty.bv]
  | .bclr => [Ty.bv, Ty.bv]
  | .bext => [Ty.bv, Ty.bv]
  | .binv => [Ty.bv, Ty.bv]
  | .bset  => [Ty.bv, Ty.bv]
  | .bclri (shamt : BitVec 6) => [Ty.bv]
  | .bexti (shamt : BitVec 6) => [Ty.bv]
  | .binvi (shamt : BitVec 6) => [Ty.bv]
  | .bseti (shamt : BitVec 6) => [Ty.bv]
  | .rolw => [Ty.bv, Ty.bv]
  | .rorw => [Ty.bv, Ty.bv]
  | .add.uw => [Ty.bv, Ty.bv]
  | .sh1add.uw => [Ty.bv, Ty.bv]
  | .sh2add.uw => [Ty.bv, Ty.bv]
  | .sh3add.uw => [Ty.bv, Ty.bv]
  | .sh1add => [Ty.bv, Ty.bv]
  | .sh2add => [Ty.bv, Ty.bv]
  | .sh3add => [Ty.bv, Ty.bv]

/--
Specifing the `outTy` of each `RISCV64` operation.
Again, we mark  it as `simp` and `reducible`.
-/

@[simp, reducible]
def Op.outTy : Op  → Ty
  |.li _ => Ty.bv
  |.mulu  => Ty.bv
  |.mulh  => Ty.bv
  |.mulhu  => Ty.bv
  |.mulhsu  => Ty.bv
  |.divu =>  Ty.bv
  |.rol => Ty.bv
  |.ror => Ty.bv
  |.remwu  => Ty.bv
  |.remu  =>  Ty.bv
  |.addiw (imm : BitVec 12) => Ty.bv
  |.lui (imm : BitVec 20) => Ty.bv
  |.auipc (imm : BitVec 20) => Ty.bv
  |.slliw (shamt : BitVec 5) => Ty.bv
  |.srliw (shamt : BitVec 5) => Ty.bv
  |.sraiw (shamt : BitVec 5) => Ty.bv
  |.slli (shamt : BitVec 6) => Ty.bv
  |.srli (shamt : BitVec 6) => Ty.bv
  |.srai (shamt : BitVec 6) => Ty.bv -- to do
  |.addw => Ty.bv
  |.subw => Ty.bv
  |.sllw => Ty.bv
  |.srlw => Ty.bv
  |.sraw => Ty.bv
  |.add => Ty.bv
  |.slt => Ty.bv
  |.sltu => Ty.bv
  |.and => Ty.bv
  |.or => Ty.bv
  |.xor => Ty.bv
  |.sll => Ty.bv
  |.srl => Ty.bv
  |.sub => Ty.bv
  |.sra => Ty.bv
  |.remw  => Ty.bv
  |.rem =>  Ty.bv
  |.mul => Ty.bv
  |.mulw => Ty.bv
  |.div=>  Ty.bv
  |.divw  =>  Ty.bv
  |.divwu  =>  Ty.bv
  |.addi (imm : BitVec 12) => Ty.bv
  |.slti (imm : BitVec 12) => Ty.bv
  |.sltiu (imm : BitVec 12) => Ty.bv
  |.andi (imm : BitVec 12) => Ty.bv
  |.ori (imm : BitVec 12) => Ty.bv
  |.xori (imm : BitVec 12) => Ty.bv
  |.czero.eqz =>   Ty.bv
  |.czero.nez =>  Ty.bv
  |.sext.b => Ty.bv
  |.sext.h => Ty.bv
  |.zext.h => Ty.bv
  |.bclr => Ty.bv
  |.bext => Ty.bv
  |.binv => Ty.bv
  |.bset  => Ty.bv
  |.bclri (shamt : BitVec 6) => Ty.bv
  |.bexti (shamt : BitVec 6) => Ty.bv
  |.binvi (shamt : BitVec 6) => Ty.bv
  |.bseti (shamt : BitVec 6) => Ty.bv
  |.rolw => Ty.bv
  |.rorw => Ty.bv
  | .add.uw => Ty.bv
  | .sh1add.uw => Ty.bv
  | .sh2add.uw => Ty.bv
  | .sh3add.uw => Ty.bv
  | .sh1add => Ty.bv
  | .sh2add => Ty.bv
  | .sh3add => Ty.bv


/-- Combine `outTy` and `sig` together into a `Signature`. -/
@[simp, reducible]
def Op.signature : Op → Signature (Ty) :=
  fun o => {sig := Op.sig o, outTy := Op.outTy o, regSig := []}


/--
Bundling the `Ops`and `Ty`into a dialect and abbreviating `RISCV64` into a dialect named `RV64`.
We pass our `Op.signature` as an instance -/
@[simp]
abbrev RV64 : Dialect where
  Op := Op
  Ty := Ty

instance : DialectSignature RV64 := ⟨Op.signature⟩



-- DEBUG: only addapted the get0 get1 of the instruction that where used in the insteuction selcetion so far, to be extended
-- I assume the layout is add (then all the args in the op code) (then args in the signature) ret_val

/--
## Dialect semantics

We assign semantics defined in `RV64` to each operation. This defines the meaning of each operation in Lean.

When writting RISC-V-like abstract MLIR ISA intutivly we write `op  arg1 arg2`. The `RISCV64` are defined to
first process the second operand then the first. Therefore we first pass `.get 1` then `.get 0` into the
functions that define our semantics.
-/
@[simp, reducible]
instance : DialectDenote (RV64) where
  denote
  |.li imm, _ , _ =>  BitVec.ofInt 64 imm
  |.addiw imm, regs, _   => ADDIW_pure64 imm (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.lui imm,  regs , _   => UTYPE_pure64_lui imm (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.auipc imm, regs, _  => UTYPE_pure64_AUIPC imm (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.slliw shamt, regs, _  => pure_semantics.SHIFTIWOP_pure64_RISCV_SLLIW_bv  shamt (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.srliw shamt, regs, _  => pure_semantics.SHIFTIWOP_pure64_RISCV_SRLIW_bv shamt (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.sraiw shamt, regs, _  =>pure_semantics.SHIFTIWOP_pure64_RISCV_SRAIW_bv shamt (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.slli shamt, regs, _  => pure_semantics.SHIFTIOP_pure64_RISCV_SLLI_bv shamt (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.srli shamt, regs, _  => pure_semantics.SHIFTIOP_pure64_RISCV_SRLI_bv shamt (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.srai shamt, regs, _  =>  pure_semantics.SHIFTIOP_pure64_RISCV_SRAI_bv shamt  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  -- The semantics are defined such that the first argument is the 2nd operand. see Semantics.lean
  |.addw, regs, _  =>  RTYPEW_pure64_RISCV_ADDW (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.subw, regs, _  => RTYPEW_pure64_RISCV_SUBW (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.sllw, regs, _  => pure_semantics.RTYPEW_pure64_RISCV_SLLW_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.srlw, regs, _  => pure_semantics.RTYPEW_pure64_RISCV_SRLW_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.sraw, regs, _ =>  pure_semantics.RTYPEW_pure64_RISCV_SRAW_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.add, regs, _ => RTYPE_pure64_RISCV_ADD (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.slt, regs, _ => RTYPE_pure64_RISCV_SLT (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.sltu, regs, _ => RTYPE_pure64_RISCV_SLTU (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.and, regs, _ => RTYPE_pure64_RISCV_AND (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.or, regs, _ => RTYPE_pure64_RISCV_OR (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.xor, regs, _ => RTYPE_pure64_RISCV_XOR (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.sll, regs, _ =>  pure_semantics.RTYPE_pure64_RISCV_SLL_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.srl, regs, _ => pure_semantics.RTYPE_pure64_RISCV_SRL_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.sub, regs, _  => RTYPE_pure64_RISCV_SUB (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.sra, regs, _  => pure_semantics.RTYPE_pure64_RISCV_SRA_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.remw, regs, _  => pure_semantics.REMW_pure64_signed_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.remwu, regs, _  => pure_semantics.REMW_pure64_unsigned_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.rem, regs, _  =>   pure_semantics.REM_pure64_signed_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.remu, regs, _ =>  pure_semantics.REM_pure64_unsigned_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.mulu, regs, _ => pure_semantics.MUL_pure64_fff_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature])) -- double check
  --|.mul false false true , regs, _ => RV64.MUL_pure64_fft (regs.getN 0 (by simp [DialectSignature.sig, signature]))  (regs.getN 1 (by simp [DialectSignature.sig, signature])) :: no corresponding RISC-V exists
  --|.mul  false true false , regs, _ => RV64.MUL_pure64_ftf (regs.getN 0 (by simp [DialectSignature.sig, signature]))  (regs.getN 1 (by simp [DialectSignature.sig, signature])) :: no corresponding RISC-V exists
  |.mulhu,regs, _ => pure_semantics.MUL_pure64_tff_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.mul ,regs, _ =>pure_semantics.MUL_pure64_ftt_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  --|.mul  true false true,regs, _ => RV64.MUL_pure64_tft (regs.getN 0 (by simp [DialectSignature.sig, signature]))  (regs.getN 1 (by simp [DialectSignature.sig, signature])) :: no corresponding RISC-V exists
  |.mulhsu ,regs, _ => pure_semantics.MUL_pure64_ttf_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.mulh,regs, _ =>pure_semantics.MUL_pure64_ttt_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.mulw,  regs, _ => pure_semantics.MULW_pure64_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature])) -- double check
  |.div, regs, _  =>  pure_semantics.DIV_pure64_signed_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.divu,  regs, _ => pure_semantics.DIV_pure64_unsigned_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.divw, regs, _  => pure_semantics.DIVW_pure64_signed (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.divwu, regs, _ =>  DIVW_pure64_unsigned (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.addi imm, reg, _  => ITYPE_pure64_RISCV_ADDI  imm (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.slti imm, reg, _  => ITYPE_pure64_RISCV_SLTI  imm (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.sltiu imm, reg, _ => ITYPE_pure64_RISCV_SLTIU  imm (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.andi imm, reg, _=> ITYPE_pure64_RISCV_ANDI  imm (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.ori imm, reg, _ => ITYPE_pure64_RISCV_ORI  imm (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.xori imm, reg, _=> ITYPE_pure64_RISCV_XORI  imm (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.czero.eqz, regs, _ => ZICOND_RTYPE_pure64_RISCV_CZERO_EQZ (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.czero.nez, regs, _ => ZICOND_RTYPE_pure64_RISCV_RISCV_CZERO_NEZ (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.sext.b, reg, _ => ZBB_EXTOP_pure64_RISCV_SEXTB (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.sext.h, reg, _ => ZBB_EXTOP_pure64_RISCV_SEXTH (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.zext.h, reg, _ => ZBB_EXTOP_pure64_RISCV_ZEXTH (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.bclr, regs, _  => pure_semantics.ZBS_RTYPE_pure64_RISCV_BCLR_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.bext, regs, _  => pure_semantics.ZBS_RTYPE_pure64_RISCV_BEXT_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.binv, regs, _  => pure_semantics.ZBS_RTYPE_pure64_BINV_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.bset, regs, _   => pure_semantics.ZBS_RTYPE_pure64_RISCV_BSET_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.bclri shamt , reg, _  => pure_semantics.ZBS_IOP_pure64_RISCV_BCLRI_bv (shamt) (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.bexti shamt, reg, _  => pure_semantics.ZBS_IOP_pure64_RISCV_BEXTI_bv (shamt) (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.binvi shamt, reg, _ => pure_semantics.ZBS_IOP_pure64_RISCV_BINVI_bv (shamt) (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.bseti shamt, reg, _ => pure_semantics.ZBS_IOP_pure64_RISCV_BSETI_bv (shamt) (reg.getN 0 (by simp [DialectSignature.sig, signature]))
  |.rolw, regs, _ => ZBB_RTYPEW_pure64_RISCV_ROLW (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.rorw, regs, _ => ZBB_RTYPEW_pure64_RISCV_RORW (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.rol, regs, _ => pure_semantics.ZBB_RTYPE_pure64_RISCV_ROL_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  |.ror, regs, _ => pure_semantics.ZBB_RTYPE_pure64_RISCV_ROR_bv (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  | .add.uw, regs, _  =>  ZBA_RTYPEUW_pure64_RISCV_ADDUW (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  | .sh1add.uw , regs, _  =>  ZBA_RTYPEUW_pure64_RISCV_SH1ADDUW (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  | .sh2add.uw, regs, _  =>  ZBA_RTYPEUW_pure64_RISCV_SH2ADDUW (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  | .sh3add.uw, regs, _  =>  ZBA_RTYPEUW_pure64_RISCV_SH3ADDUW (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  | .sh1add, regs, _  =>  ZBA_RTYPE_pure64_RISCV_SH1ADD (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  | .sh2add, regs, _  =>  ZBA_RTYPE_pure64_RISCV_SH2ADD (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
  | .sh3add, regs, _  =>  ZBA_RTYPE_pure64_RISCV_SH3ADD (regs.getN 1 (by simp [DialectSignature.sig, signature]))  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
end RISCV64
/-

/-

def_denote for RV64 where
  |.li imm =>  BitVec.ofInt 64 imm
  |.addiw imm => λ rs1 =>  ADDIW_pure64 imm rs1
  |.lui imm => λ rs1 => UTYPE_pure64_lui imm rs1
  |.auipc imm => λ rs1 => UTYPE_pure64_AUIPC imm rs1
  |.slliw shamt => λ rs1 => pure_semantics.SHIFTIWOP_pure64_RISCV_SLLIW_bv shamt rs1
  |.srliw shamt => λ rs1 => pure_semantics.SHIFTIWOP_pure64_RISCV_SRLIW_bv shamt rs1
  |.sraiw shamt => λ rs1 => pure_semantics.SHIFTIWOP_pure64_RISCV_SRAIW_bv shamt rs1
  |.srli shamt => λ rs1 => pure_semantics.SHIFTIOP_pure64_RISCV_SRLI_bv shamt rs1
  |.slli shamt => λ rs1 => pure_semantics.SHIFTIOP_pure64_RISCV_SLLI_bv shamt rs1
  |.srai shamt => λ rs1 => pure_semantics.SHIFTIOP_pure64_RISCV_SRAI_bv shamt  rs1
  |.addw => λ rs1 rs2 => RTYPEW_pure64_RISCV_SUBW rs2  rs1
  |.subw => λ rs1 rs2 => RTYPEW_pure64_RISCV_SUBW rs2 rs1
  |.sllw => λ rs1 rs2 => pure_semantics.RTYPEW_pure64_RISCV_SLLW_bv rs2 rs1
  |.srlw => λ rs1 rs2 => pure_semantics.RTYPEW_pure64_RISCV_SRLW_bv rs2  rs1
  |.sraw => λ rs1 rs2 => pure_semantics.RTYPEW_pure64_RISCV_SRAW_bv rs2 rs1
  |.add => λ rs1 rs2 => RTYPE_pure64_RISCV_ADD rs2 rs1
  |.slt => λ rs1 rs2 => RTYPE_pure64_RISCV_SLT rs2 rs1
  |.sltu => λ rs1 rs2 => RTYPE_pure64_RISCV_SLTU rs2 rs1
  |.and => λ rs1 rs2 => RTYPE_pure64_RISCV_AND rs2 rs1
  |.or => λ rs1 rs2 => RTYPE_pure64_RISCV_OR rs2 rs1
  |.xor => λ rs1 rs2 => RTYPE_pure64_RISCV_XOR rs2 rs1
  |.sll => λ rs1 rs2 => pure_semantics.RTYPE_pure64_RISCV_SLL_bv rs2 rs1
  |.srl => λ rs1 rs2 => pure_semantics.RTYPE_pure64_RISCV_SRL_bv rs2 rs1
  |.sub => λ rs1 rs2 => RTYPE_pure64_RISCV_SUB rs2 rs1
  |.sra => λ rs1 rs2 =>  pure_semantics.RTYPE_pure64_RISCV_SRA_bv rs2 rs1
  |.remw => λ rs1 rs2 => pure_semantics.REMW_pure64_signed_bv rs2 rs1
  |.remwu => λ rs1 rs2 => pure_semantics.REMW_pure64_unsigned_bv rs2 rs1
  |.rem => λ rs1 rs2 => pure_semantics.REM_pure64_signed_bv rs2 rs1
  |.remu => λ rs1 rs2 => pure_semantics.REM_pure64_unsigned rs2 rs1
  |.mulu => λ rs1 rs2 => pure_semantics.MUL_pure64_fff_bv rs2 rs1
  |.mulhu => λ rs1 rs2 => pure_semantics.MUL_pure64_tff_bv rs2 rs1
  |.mul => λ rs1 rs2 => pure_semantics.MUL_pure64_ftt_bv rs2 rs1
  |.mulhsu => λ rs1 rs2 =>  pure_semantics.MUL_pure64_ttf_bv rs2 rs1
  |.mulh => λ rs1 rs2 => pure_semantics.MUL_pure64_ttt_bv rs2 rs1
  |.mulw => λ rs1 rs2 => pure_semantics.MULW_pure64_bv rs2 rs1
  |.div => λ rs1 rs2 => pure_semantics.DIV_pure64_signed_bv rs2 rs1
  |.divu => λ rs1 rs2 => pure_semantics.DIV_pure64_unsigned_bv rs2 rs1
  |.divw => λ rs1 rs2 => pure_semantics.DIVW_pure64_signed rs2 rs1 -- still need to rewrite it
  |.divwu => λ rs1 rs2 => DIVW_pure64_unsigned rs2 rs1 -- same here
  |.addi imm => λ rs1 => ITYPE_pure64_RISCV_ADDI  imm rs1
  |.slti imm => λ rs1 => ITYPE_pure64_RISCV_SLTI  imm rs1
  |.sltiu imm => λ rs1 => ITYPE_pure64_RISCV_SLTIU  imm rs1
  |.andi imm => λ rs1 => ITYPE_pure64_RISCV_ANDI  imm rs1
  |.ori imm => λ rs1 => ITYPE_pure64_RISCV_ORI  imm rs1
  |.xori imm => λ rs1 => ITYPE_pure64_RISCV_XORI  imm rs1
  |.czero.eqz => λ rs1 rs2 => ZICOND_RTYPE_pure64_RISCV_CZERO_EQZ rs2 rs1
  |.czero.nez => λ rs1 rs2 => ZICOND_RTYPE_pure64_RISCV_RISCV_CZERO_NEZ rs2 rs1
  |.sext.b => λ rs1 => ZBB_EXTOP_pure64_RISCV_SEXTB rs1
  |.sext.h => λ rs1 => ZBB_EXTOP_pure64_RISCV_SEXTH rs1
  |.zext.h => λ rs1 => ZBB_EXTOP_pure64_RISCV_ZEXTH rs1
  |.bclr => λ rs1 rs2 => pure_semantics.ZBS_RTYPE_pure64_RISCV_BCLR_bv rs2 rs1
  |.bext => λ rs1 rs2=> pure_semantics.ZBS_RTYPE_pure64_RISCV_BEXT_bv rs2 rs1
  |.binv => λ rs1 rs2 => pure_semantics.ZBS_RTYPE_pure64_BINV_bv rs2 rs1
  |.bset => λ rs1 rs2=> pure_semantics.ZBS_RTYPE_pure64_RISCV_BSET_bv rs2 rs1
  |.bclri shamt => λ rs1 => pure_semantics.ZBS_IOP_pure64_RISCV_BCLRI_bv shamt rs1
  |.bexti shamt => λ rs1 => pure_semantics.ZBS_IOP_pure64_RISCV_BEXTI_bv shamt rs1
  |.binvi shamt => λ rs1 => pure_semantics.ZBS_IOP_pure64_RISCV_BINVI_bv shamt rs1
  |.bseti shamt  => λ rs1 => pure_semantics.ZBS_IOP_pure64_RISCV_BSETI_bv shamt rs1
  |.rolw => λ rs1 rs2 => ZBB_RTYPEW_pure64_RISCV_ROLW rs2 rs1
  |.rorw => λ rs1 rs2 => ZBB_RTYPEW_pure64_RISCV_RORW rs2 rs1
  |.rol => λ rs1 rs2 => pure_semantics.ZBB_RTYPE_pure64_RISCV_ROL_bv rs2 rs1
  |.ror => λ rs1 rs2 => pure_semantics.ZBB_RTYPE_pure64_RISCV_ROR_bv rs2 rs1
  |.add.uw => λ rs1 rs2 => ZBA_RTYPEUW_pure64_RISCV_ADDUW rs2 rs1
  |.sh1add.uw => λ rs1 rs2 => ZBA_RTYPEUW_pure64_RISCV_SH1ADDUW rs2 rs1
  |.sh2add.uw => λ rs1 rs2 => ZBA_RTYPEUW_pure64_RISCV_SH2ADDUW rs2 rs1
  |.sh3add.uw => λ rs1 rs2 => ZBA_RTYPEUW_pure64_RISCV_SH3ADDUW rs2 rs1
  |.sh1add => λ rs1 rs2 => ZBA_RTYPE_pure64_RISCV_SH1ADD rs2 rs1
  |.sh2add => λ rs1 rs2 => ZBA_RTYPE_pure64_RISCV_SH2ADD rs2 rs1
  |.sh3add => λ rs1 rs2 => ZBA_RTYPE_pure64_RISCV_SH3ADD rs2 rs1
-/


-/
