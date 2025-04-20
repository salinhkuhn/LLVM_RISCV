import LeanRV64DLEAN.Sail.Sail
import LeanRV64DLEAN.Sail.BitVec
import LeanRV64DLEAN.Defs
import LeanRV64DLEAN.Specialization
import LeanRV64DLEAN.RiscvExtras
import LeanRV64DLEAN
import LeanRV64DLEAN.pure_func
import RiscvDialect.Dialect
-- import RiscvDialect.TacticSail

open Functions
open Retired
open Sail
open PureFunctions

-- pure functions modell <-> pure BitVec domain lowering :: now -> pure function <-> dialect operations definiton
-- missing BitVector Lemmas:

-- @[simp]
theorem extractLsb'_extractLsb' :
    BitVec.extractLsb' start length (BitVec.extractLsb' start' length' x)
    = (BitVec.extractLsb' (start'+start) (min length length') x).setWidth length := by
  sorry

-- @[simp]
theorem extractLsb'_extractLsb'2 {x : BitVec w} :
    BitVec.extractLsb' start length (BitVec.extractLsb' start' length' x)
    = BitVec.extractLsb' (start'+start) length (x.setWidth (start + start' + (min length length'))) := by
  -- obtain rfl : w = 16 := sorry
  -- bv_decide
  --unfold BitVec.extractLsb'
  --simp
  sorry


theorem extractLsb'_zero : BitVec.extractLsb' 0 length x  = BitVec.setWidth length x := by
  unfold BitVec.extractLsb'
  simp only [Nat.shiftRight_zero, BitVec.ofNat_toNat]


theorem setWidth_extractLsb' (n w: Nat) (x : BitVec w) :
    BitVec.setWidth n x = BitVec.extractLsb' 0 n x := by
      simp only [BitVec.extractLsb', Nat.shiftRight_zero, BitVec.ofNat_toNat]

-- proved the sign extension of zero vector is again zero
theorem  sign_extend_zero (w1 w2 : Nat) (h : w1 ≤ w2) :
    sign_extend (0#w1)   = 0#w2 := by
    rw [sign_extend]
    rw [Sail.BitVec.signExtend]
    rw [BitVec.signExtend]
    simp


-- SAIL FIX: to overcome the redefinition of operators in SAIL

theorem add_set_Width_eq (x : BitVec w1) (y : BitVec w1) :
    BitVec.add x y =  x + y  := by
      simp
      simp only [_dd.hAdd, BitVec.setWidth_eq]

theorem add_set_Width (x : BitVec w1) (y : BitVec w2) :
    BitVec.add x y =  x + y  := by
      simp [HAdd.hAdd]


-- SECTION WHERE I PROVE THAT EACH RISC-V INSTRUCTION CORRESPONDS TO SIMPLER BIT VECTOR INSTRUCTIONS
-- SIMPLIFICATION OF RISC-V SEMANTICS TO BITVECTORS and writting coorespodnig proofs
-- pure functions modell <-> pure BitVec domain lowering

theorem execute_ADDIW_pure64_BitVec (imm : BitVec 12) (rs1_val : BitVec 64) :
  PureFunctions.execute_ADDIW_pure64 imm rs1_val =
     BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.add (BitVec.signExtend 64 imm) rs1_val)) := by
  unfold PureFunctions.execute_ADDIW_pure64
  simp
  unfold sign_extend
  unfold Sail.BitVec.signExtend
  unfold Sail.BitVec.extractLsb
  rw [BitVec.extractLsb]
  rw [← setWidth_extractLsb']
  unfold HPow.hPow
  unfold instHPowInt_leanRV64DLEAN
  bv_decide

-- File containing the proofs that my dialect semantics directly corresponds to executing the pure function extracted from Sail.
-- RV64 refers to the MLIR-style dialect for RISCV

-- changing the proofs such that rhs is directly the sail pure function without copying the bit vector directly
theorem execute_UTYPE_pure64_lui (imm : BitVec 20) (pc : BitVec 64) : PureFunctions.execute_UTYPE_pure64 imm pc (uop.RISCV_LUI)
    = RV64.UTYPE_pure64_lui imm pc:= by
  unfold RV64.UTYPE_pure64_lui
  unfold PureFunctions.execute_UTYPE_pure64
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  unfold sign_extend Sail.BitVec.signExtend BitVec.signExtend
  unfold HAppend.hAppend HPow.hPow instHPowInt_leanRV64DLEAN BitVec.instHAppendHAddNat
  bv_decide

-- loads immediate into upper 20 bits and then fills the rest up with 0 and returns, adds the program counter and then returns it as a result
theorem execute_UTYPE_pure64_AUIPC (imm : BitVec 20) (pc : BitVec 64)  : PureFunctions.execute_UTYPE_pure64 imm pc (uop.RISCV_AUIPC)
    = RV64.UTYPE_pure64_AUIPC imm pc:= by
  unfold RV64.UTYPE_pure64_AUIPC PureFunctions.execute_UTYPE_pure64
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_eq, BitVec.add_left_inj]
  unfold sign_extend Sail.BitVec.signExtend BitVec.signExtend
  unfold HAppend.hAppend HPow.hPow instHPowInt_leanRV64DLEAN BitVec.instHAppendHAddNat
  bv_decide

-- shiftiwop semantics:
theorem execute_SHIFTIWOP_pure64_RISCV_SLLIW (shamt : BitVec 5) (rs1_val : BitVec 64) :  PureFunctions.execute_SHIFTIWOP_pure64 shamt (sopw.RISCV_SLLIW) rs1_val
    = RV64.SHIFTIWOP_pure64_RISCV_SLLIW shamt  rs1_val := by
  unfold  RV64.SHIFTIWOP_pure64_RISCV_SLLIW PureFunctions.execute_SHIFTIWOP_pure64
  simp only [BitVec.shiftLeft_eq]
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb  BitVec.signExtend
  rw [BitVec.extractLsb]
  unfold  shift_bits_left HPow.hPow HShiftLeft.hShiftLeft BitVec.instHShiftLeftNat instHPowInt_leanRV64DLEAN BitVec.instHShiftLeft
  bv_decide


-- logical rightshift, filled with zeros x/2^s rounding down
theorem execute_SHIFTIWOP_pure64_RISCV_SRLIW (shamt : BitVec 5) (rs1_val : BitVec 64)  :  PureFunctions.execute_SHIFTIWOP_pure64 shamt (sopw.RISCV_SRLIW) rs1_val
    = RV64.SHIFTIWOP_pure64_RISCV_SRLIW shamt rs1_val:= by
  unfold RV64.SHIFTIWOP_pure64_RISCV_SRLIW PureFunctions.execute_SHIFTIWOP_pure64
  simp only [BitVec.ushiftRight_eq]
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb  BitVec.signExtend
  rw [BitVec.extractLsb]--- to rewrite into Lsb'
  unfold  shift_bits_right HPow.hPow HShiftRight.hShiftRight  instHPowInt_leanRV64DLEAN BitVec.instHShiftRightNat BitVec.instHShiftRight
  bv_decide

theorem execute_SHIFTIWOP_pure64_RISCV_SRAIW (shamt : BitVec 5) (rs1_val : BitVec 64) :
  PureFunctions.execute_SHIFTIWOP_pure64 shamt sopw.RISCV_SRAIW rs1_val
    =
    RV64.SHIFTIWOP_pure64_RISCV_SRAIW shamt rs1_val := by rfl

theorem execute_SHIFTIOP_pure64_RISCV_SLLI (shamt : BitVec 6) (rs1_val : BitVec 64)  : PureFunctions.execute_SHIFTIOP_pure64 shamt sop.RISCV_SLLI rs1_val
    = RV64.SHIFTIOP_pure64_RISCV_SLLI shamt rs1_val:= by
  unfold  RV64.SHIFTIOP_pure64_RISCV_SLLI PureFunctions.execute_SHIFTIOP_pure64
  simp
  unfold shift_bits_left HShiftLeft.hShiftLeft BitVec.instHShiftLeft BitVec.instHShiftLeftNat
  bv_decide

theorem execute_SHIFTIOP_pure64_RISCV_SRLI (shamt : BitVec 6) (rs1_val : BitVec 64) : PureFunctions.execute_SHIFTIOP_pure64 shamt sop.RISCV_SRLI rs1_val
    = RV64.SHIFTIOP_pure64_RISCV_SRLI shamt  rs1_val := by
  unfold RV64.SHIFTIOP_pure64_RISCV_SRLI PureFunctions.execute_SHIFTIOP_pure64
  simp
  unfold shift_bits_right HShiftRight.hShiftRight BitVec.instHShiftRight BitVec.instHShiftRightNat
  bv_decide

theorem execute_SHIFTIOP_pure64_RISCV_SRAI (shamt : (BitVec 6)) (rs1_val : (BitVec 64)) : PureFunctions.execute_SHIFTIOP_pure64 shamt sop.RISCV_SRAI rs1_val =
    RV64.SHIFTIOP_pure64_RISCV_SRAI shamt  rs1_val:=
  by
  rfl

-- simple integer operations on 32-bit word and then sign extend result to 64 bits
theorem execute_RTYPEW_pure64_RISCV_ADDW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPEW_pure64 ropw.RISCV_ADDW rs2_val rs1_val =
      RV64.RTYPEW_pure64_RISCV_ADDW rs2_val rs1_val := by
  unfold RV64.RTYPEW_pure64_RISCV_ADDW PureFunctions.execute_RTYPEW_pure64
  simp only [Nat.sub_zero, Nat.reduceAdd, BitVec.add_eq]
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb HPow.hPow instHPowInt_leanRV64DLEAN
  bv_decide

theorem execute_RTYPEW_pure64_RISCV_SUBW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPEW_pure64 (ropw.RISCV_SUBW) (rs2_val) (rs1_val) =
      RV64.RTYPEW_pure64_RISCV_SUBW rs2_val rs1_val := by
    unfold  RV64.RTYPEW_pure64_RISCV_SUBW PureFunctions.execute_RTYPEW_pure64
    simp only [Nat.sub_zero, Nat.reduceAdd, BitVec.sub_eq]
    unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb HPow.hPow instHPowInt_leanRV64DLEAN
    bv_decide

-- can be all done by rfl
theorem execute_RTYPEW_pure64_RISCV_SLLW (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : PureFunctions.execute_RTYPEW_pure64 ropw.RISCV_SLLW rs2_val rs1_val =
    RV64.RTYPEW_pure64_RISCV_SLLW rs2_val rs1_val := by
  unfold RV64.RTYPEW_pure64_RISCV_SLLW PureFunctions.execute_RTYPEW_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb BitVec.signExtend
  unfold  shift_bits_left HPow.hPow HShiftLeft.hShiftLeft BitVec.instHShiftLeftNat instHPowInt_leanRV64DLEAN BitVec.instHShiftLeft
  simp only [Int.reduceToNat, Int.reducePow, Int.reduceMul, BitVec.extractLsb_toNat,
    Nat.shiftRight_zero, Nat.sub_zero, Nat.reduceAdd, Nat.reducePow, Nat.reduceDvd,
    Nat.mod_mod_of_dvd, BitVec.toInt_shiftLeft, BitVec.shiftLeft_eq, BitVec.extractLsb'_toNat]

-- can be all done by rfl
theorem execute_RTYPEW_pure64_RISCV_SRLW (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : PureFunctions.execute_RTYPEW_pure64 ropw.RISCV_SRLW rs2_val rs1_val
    = RV64.RTYPEW_pure64_RISCV_SRLW rs2_val  rs1_val:= by
  unfold RV64.RTYPEW_pure64_RISCV_SRLW PureFunctions.execute_RTYPEW_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb BitVec.signExtend
  rw [BitVec.extractLsb]
  unfold  shift_bits_right HPow.hPow HShiftRight.hShiftRight BitVec.instHShiftRightNat instHPowInt_leanRV64DLEAN BitVec.instHShiftRight
  simp only [Int.reduceToNat, Int.reducePow, Int.reduceMul, Nat.sub_zero, Nat.reduceAdd,
    BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow, Nat.reduceDvd, Nat.mod_mod_of_dvd,
    BitVec.toInt_ushiftRight, BitVec.extractLsb'_toNat, BitVec.ushiftRight_eq]

-- SUBSECTION WHERE MADE THEOIREMS FOR REWRITTING TO THE CORE INSTANCE

@[simp] theorem sail_hPow_eq (x y : Int) : x ^ y  = x ^ y.toNat := by rfl

-- very ugly
theorem execute_RTYPEW_pure64_RISCV_SRAW (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) :
    PureFunctions.execute_RTYPEW_pure64 (ropw.RISCV_SRAW) rs2_val rs1_val
      = BitVec.signExtend 64
           (BitVec.setWidth 32
              (BitVec.extractLsb
                 (31 + rs2_val.toNat % 4294967296 % 32)
                     (rs2_val.toNat % 4294967296 % 32)
                          (BitVec.signExtend (32 + rs2_val.toNat % 4294967296 % 32)
                              (BitVec.extractLsb 31 0 rs1_val)))) := by rfl


theorem execute_RTYPE_pure64_RISCV_ADD (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_ADD  rs2_val rs1_val
      = RV64.RTYPE_pure64_RISCV_ADD rs2_val rs1_val:= by rfl

theorem execute_RTYPE_pure64_RISCV_SLT (rs2_val : BitVec 64) (rs1_val : BitVec 64) : PureFunctions.execute_RTYPE_pure64 rop.RISCV_SLT rs2_val rs1_val
  =  RV64.RTYPE_pure64_RISCV_SLT rs2_val rs1_val := by rfl

theorem execute_RTYPE_pure64_RISCV_SLTU (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_SLTU rs2_val rs1_val
    = RV64.RTYPE_pure64_RISCV_SLTU rs2_val rs1_val := by rfl

theorem execute_RTYPE_pure64_RISCV_AND (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_AND rs2_val rs1_val
      = RV64.RTYPE_pure64_RISCV_AND rs2_val rs1_val := by
  unfold RV64.RTYPE_pure64_RISCV_AND PureFunctions.execute_RTYPE_pure64
  bv_decide

theorem execute_RTYPE_pure64_RISCV_OR(rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_OR  rs2_val rs1_val
      = RV64.RTYPE_pure64_RISCV_OR rs2_val rs1_val:= by
  unfold RV64.RTYPE_pure64_RISCV_OR PureFunctions.execute_RTYPE_pure64
  bv_decide

theorem execute_RTYPE_pure64_RISCV_XOR(rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_XOR  rs2_val  rs1_val
      = RV64.RTYPE_pure64_RISCV_XOR rs2_val rs1_val:= by
  unfold RV64.RTYPE_pure64_RISCV_XOR PureFunctions.execute_RTYPE_pure64
  bv_decide

theorem execute_RTYPE_pure64_RISCV_SLL (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
     PureFunctions.execute_RTYPE_pure64 rop.RISCV_SLL  rs2_val rs1_val =
      RV64.RTYPE_pure64_RISCV_SLL rs2_val rs1_val:= by rfl

theorem execute_RTYPE_pure64_RISCV_SRL (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_SRL rs2_val rs1_val
      = RV64.RTYPE_pure64_RISCV_SRL rs2_val rs1_val:= by rfl

theorem execute_RTYPE_pure64_RISCV_SUB (rs2_val : BitVec 64) (rs1_val : BitVec 64) : PureFunctions.execute_RTYPE_pure64 rop.RISCV_SUB  rs2_val rs1_val
    = RV64.RTYPE_pure64_RISCV_SUB rs2_val rs1_val:= by
  unfold RV64.RTYPE_pure64_RISCV_SUB PureFunctions.execute_RTYPE_pure64
  bv_decide

theorem execute_RTYPE_pure64_RISCV_SRA (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_RTYPE_pure64 rop.RISCV_SRA rs2_val rs1_val
      = RV64.RTYPE_pure64_RISCV_SRA rs2_val rs1_val := by
      unfold RV64.RTYPE_pure64_RISCV_SRA
      rfl

theorem execute_REMW_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_REMW_pure64 False rs2_val rs1_val
    = RV64.REMW_pure64_unsigned rs2_val rs1_val  := by
  unfold RV64.REMW_pure64_unsigned execute_REMW_pure64 sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb to_bits get_slice_int
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Nat.reduceAdd,
    decide_false, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, BitVec.extractLsb_toNat,
    Nat.shiftRight_zero, Nat.reducePow, Int.ofNat_emod, Nat.cast_ofNat, beq_iff_eq, Int.ofNat_toNat,
    Int.ofNat_eq_coe]



theorem execute_REMW_pure64_signed :
    PureFunctions.execute_REMW_pure64 (True) (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) =
     RV64.REMW_pure64_signed (rs2_val) (rs1_val) := by
  unfold RV64.REMW_pure64_signed execute_REMW_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb to_bits get_slice_int
  rw [← Int.ofNat_eq_coe]
  simp

--tmod was hard
theorem execute_REM_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_REM_pure64 (False) rs2_val rs1_val =
    RV64.REM_pure64_unsigned rs2_val rs1_val
  := by
  unfold RV64.REM_pure64_unsigned execute_REM_pure64
  simp only [decide_false, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, Int.ofNat_eq_coe,
    Int.ofNat_toNat]
  unfold  to_bits get_slice_int
  rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe,← Int.ofNat_eq_coe]
  simp
  rfl


theorem execute_REM_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    PureFunctions.execute_REM_pure64 True rs2_val rs1_val
      = RV64.REM_pure64_signed rs2_val rs1_val  := by
  unfold RV64.REM_pure64_signed execute_REM_pure64
  simp
  unfold  to_bits get_slice_int Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul]
  rw [← Int.ofNat_eq_coe]
  simp only [Int.reduceToNat, Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat]


theorem  execute_MULW_pure64 (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64))  : execute_MULW_pure64 rs2_val rs1_val =
   RV64.MULW_pure64 (rs2_val) (rs1_val) := by
     rfl

theorem execute_MUL_pure64_fff (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
     execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= False, signed_rs2 := False }) rs2_val rs1_val
       = RV64.MUL_pure64_fff rs2_val rs1_val
        := by
        unfold RV64.MUL_pure64_fff  execute_MUL_pure64
        simp only [decide_false, Bool.false_eq_true, ↓reduceIte, Int.ofNat_eq_coe]
        unfold Sail.BitVec.extractLsb Functions.xlen to_bits get_slice_int
        simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub,
          Nat.reduceAdd, Int.ofNat_toNat, Int.mul_def]

theorem execute_MUL_pure64_fft (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= False, signed_rs2 := True }) rs2_val rs1_val
      = RV64.MUL_pure64_fft rs2_val rs1_val
    := by
    unfold RV64.MUL_pure64_fft execute_MUL_pure64
    simp only [decide_false, Bool.false_eq_true, ↓reduceIte, decide_true, Int.ofNat_eq_coe,
      Int.ofNat_toNat]
    unfold Sail.BitVec.extractLsb Functions.xlen
    simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
    unfold to_bits get_slice_int
    rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
    simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat, Int.mul_def]
    --bv_decide ask why this can't be recognized by bv_decide

theorem execute_MUL_pure64_ftf (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= True, signed_rs2 := False }) rs2_val rs1_val
    = RV64.MUL_pure64_ftf rs2_val rs1_val
    := by
    unfold RV64.MUL_pure64_ftf execute_MUL_pure64
    simp only [decide_false, Bool.false_eq_true, ↓reduceIte, decide_true, Int.ofNat_eq_coe,
      Int.toNat_ofNat, Int.mul_def, Int.ofNat_toNat]
    unfold Sail.BitVec.extractLsb Functions.xlen
    simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
    unfold to_bits get_slice_int
    rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
    simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat]

theorem execute_MUL_pure64_tff (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := True, signed_rs1:= False, signed_rs2 := False }) rs2_val rs1_val
      = RV64.MUL_pure64_tff rs2_val rs1_val
  := by
  unfold RV64.MUL_pure64_tff execute_MUL_pure64
  simp only [decide_true, ↓reduceIte, decide_false, Bool.false_eq_true, Int.ofNat_eq_coe,
    Int.ofNat_toNat]
  unfold Sail.BitVec.extractLsb Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
  unfold to_bits get_slice_int
  rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
  simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat, Int.mul_def]

theorem execute_MUL_pure64_tft (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := True, signed_rs1:= False, signed_rs2 := True }) rs2_val rs1_val
      = RV64.MUL_pure64_tft rs2_val rs1_val
  := by
  unfold RV64.MUL_pure64_tft execute_MUL_pure64
  simp only [decide_true, ↓reduceIte, decide_false, Bool.false_eq_true, Int.ofNat_eq_coe,
    Int.ofNat_toNat]
  unfold Sail.BitVec.extractLsb Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
  unfold to_bits get_slice_int
  rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
  simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat, Int.mul_def]


theorem execute_MUL_pure64_ttf (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := True, signed_rs1:= True, signed_rs2 := False }) rs2_val rs1_val
      = RV64.MUL_pure64_ttf rs2_val rs1_val
  := by
  unfold RV64.MUL_pure64_ttf execute_MUL_pure64
  simp only [decide_true, ↓reduceIte, decide_false, Bool.false_eq_true, Nat.reduceAdd,
    Int.ofNat_eq_coe, Int.ofNat_toNat]
  unfold Sail.BitVec.extractLsb Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
  unfold to_bits get_slice_int
  rw [← Int.ofNat_eq_coe, ← Int.ofNat_eq_coe]
  simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat, Int.mul_def]


theorem execute_MUL_pure64_ftt (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := False, signed_rs1:= True, signed_rs2 := True }) rs2_val rs1_val
      = RV64.MUL_pure64_ftt rs2_val rs1_val
  := by
  unfold RV64.MUL_pure64_ftt execute_MUL_pure64
  simp
  unfold Sail.BitVec.extractLsb Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
  unfold to_bits get_slice_int
  rw [← Int.ofNat_eq_coe]
  simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat]

theorem execute_MUL_pure64_ttt (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    execute_MUL_pure64 (mul_op := { high := True, signed_rs1:= True, signed_rs2 := True }) rs2_val rs1_val
      = RV64.MUL_pure64_ttt rs2_val rs1_val
  := by
  unfold RV64.MUL_pure64_ttt execute_MUL_pure64
  simp only [decide_true, ↓reduceIte, Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat]
  unfold Sail.BitVec.extractLsb Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub]
  unfold to_bits get_slice_int
  rw [← Int.ofNat_eq_coe]
  simp only [Nat.reduceAdd, Int.ofNat_eq_coe, Int.ofNat_toNat, Int.mul_def]


theorem excute_DIVW_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  execute_DIVW_pure64 (True) rs2_val rs1_val
    = RV64.DIVW_pure64_signed rs2_val rs1_val
  := by
  unfold RV64.DIVW_pure64_signed execute_DIVW_pure64
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, decide_true, ↓reduceIte,
    Nat.sub_zero, Nat.reduceAdd, beq_iff_eq, Int.reduceNeg, Int.reduceSub, gt_iff_lt, Bool.true_and,
    decide_eq_true_eq, Int.zero_sub]
  unfold sign_extend Sail.BitVec.signExtend to_bits get_slice_int Sail.BitVec.extractLsb
  simp only [Nat.reduceAdd, Int.reduceNeg, Int.ofNat_toNat]

--tdiv
theorem execute_DIVW_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64)
    : execute_DIVW_pure64 (False) rs2_val rs1_val
    =
    RV64.DIVW_pure64_unsigned rs2_val rs1_val
  := by
  unfold RV64.DIVW_pure64_unsigned execute_DIVW_pure64
  unfold sign_extend Sail.BitVec.signExtend to_bits get_slice_int Sail.BitVec.extractLsb
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Nat.reduceAdd,
    decide_false, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, BitVec.extractLsb_toNat,
    Nat.shiftRight_zero, Nat.reducePow, Int.ofNat_emod, Nat.cast_ofNat, beq_iff_eq, Int.reduceNeg,
    Int.reduceSub, gt_iff_lt, Bool.false_and, Int.ofNat_toNat, Int.ofNat_eq_coe]

theorem execute_DIV_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
     execute_DIV_pure64 (True) rs2_val rs1_val
      = RV64.DIV_pure64_signed rs2_val rs1_val
  := by
  unfold RV64.DIV_pure64_signed execute_DIV_pure64 to_bits get_slice_int Functions.xlen xlen_max_signed xlen_min_signed Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Nat.reduceAdd,
    decide_true, ↓reduceIte, beq_iff_eq, Int.reduceNeg, Int.reduceSub, gt_iff_lt, Bool.true_and,
    decide_eq_true_eq, zero_sub, Int.ofNat_toNat]


theorem execute_DIV_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64)
    : execute_DIV_pure64 (False) rs2_val rs1_val
    = RV64.DIV_pure64_unsigned rs2_val rs1_val
  := by
  unfold  RV64.DIV_pure64_unsigned execute_DIV_pure64
  simp only [decide_false, Bool.false_eq_true, ↓reduceIte, beq_iff_eq, Int.natCast_eq_zero,
    Int.reduceNeg, gt_iff_lt, Bool.false_and, Int.ofNat_eq_coe]
  simp [to_bits ,Functions.xlen]
  rfl

theorem execute_ITYPE_pure64_RISCV_ADDI (imm : BitVec 12) (rs1_val : BitVec 64) : PureFunctions.execute_ITYPE_pure64 imm rs1_val iop.RISCV_ADDI
    = RV64.ITYPE_pure64_RISCV_ADDI imm rs1_val := by
  unfold RV64.ITYPE_pure64_RISCV_ADDI PureFunctions.execute_ITYPE_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend --HPow.hPow instHPowInt_leanRV64DLEAN bc introdued the lemma
  bv_decide

theorem execute_ITYPE_pure64_RISCV_SLTI (imm : BitVec 12) (rs1_val : BitVec 64) :
     PureFunctions.execute_ITYPE_pure64 imm  rs1_val iop.RISCV_SLTI
       = RV64.ITYPE_pure64_RISCV_SLTI imm  rs1_val  := by rfl

theorem execute_ITYPE_pure64_RISCV_SLTIU (imm : BitVec 12) (rs1_val : BitVec 64) :
     PureFunctions.execute_ITYPE_pure64 imm  rs1_val iop.RISCV_SLTIU
       = RV64.ITYPE_pure64_RISCV_SLTIU imm  rs1_val  := by rfl

-- works also by using rfl
theorem execute_ITYPE_pure64_RISCV_ANDI (imm : BitVec 12) (rs1_val : BitVec 64) :
    PureFunctions.execute_ITYPE_pure64 imm rs1_val  iop.RISCV_ANDI
      = RV64.ITYPE_pure64_RISCV_ANDI imm rs1_val := by
  unfold RV64.ITYPE_pure64_RISCV_ANDI PureFunctions.execute_ITYPE_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend  HAnd.hAnd instHAndBitVec_leanRV64DLEAN
   instHAndOfAndOp
  bv_decide

-- works by using rfl
theorem execute_ITYPE_pure64_RISCV_ORI (imm : (BitVec 12)) (rs1_val : (BitVec 64))  :
    PureFunctions.execute_ITYPE_pure64 imm rs1_val (iop.RISCV_ORI)
      = RV64.ITYPE_pure64_RISCV_ORI imm rs1_val
  := by
  unfold RV64.ITYPE_pure64_RISCV_ORI PureFunctions.execute_ITYPE_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

-- works by using rfl
theorem execute_ITYPE_pure64_RISCV_XORI imm (rs1_val : (BitVec 64))  :
    PureFunctions.execute_ITYPE_pure64 imm rs1_val (iop.RISCV_XORI)
      = RV64.ITYPE_pure64_RISCV_XORI imm rs1_val
  := by
  unfold  RV64.ITYPE_pure64_RISCV_XORI PureFunctions.execute_ITYPE_pure64
  simp
  unfold sign_extend Sail.BitVec.signExtend
  bv_decide

theorem execute_ZICOND_RTYPE_pure64_RISCV_CZERO_EQZ (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) :
    execute_ZICOND_RTYPE_pure64 rs2_val  rs1_val zicondop.RISCV_CZERO_EQZ
      = RV64.ZICOND_RTYPE_pure64_RISCV_CZERO_EQZ rs2_val  rs1_val
  := by
  unfold execute_ZICOND_RTYPE_pure64
  simp
  unfold zeros_implicit
  rfl

theorem execute_ZICOND_RTYPE_pure64_RISCV_RISCV_CZERO_NEZ (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) :
    execute_ZICOND_RTYPE_pure64 rs2_val  rs1_val zicondop.RISCV_CZERO_NEZ
      = RV64.ZICOND_RTYPE_pure64_RISCV_RISCV_CZERO_NEZ rs2_val  rs1_val
  := by
  unfold execute_ZICOND_RTYPE_pure64
  simp
  unfold zeros_implicit
  rfl

-- tested SIMPLE PEEPHOLE REWRITES:Prove simple rewrites based on the BitVector modelling

theorem  add_zero10000 : PureFunctions.execute_ADDIW_pure64 (imm : BitVec 12) (0#64) =  BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.add (BitVec.signExtend 64 imm) 0#64))  := by
  rw [execute_ADDIW_pure64_BitVec]

theorem  zero_add100 : PureFunctions.execute_ADDIW_pure64 (0#12) (x : BitVec 64) =  BitVec.signExtend 64 (BitVec.setWidth 32 x)  := by
  rw [execute_ADDIW_pure64_BitVec]
  bv_decide
