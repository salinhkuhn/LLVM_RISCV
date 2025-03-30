import LeanRV64DLEAN.Sail.Sail
import LeanRV64DLEAN.Sail.BitVec
import LeanRV64DLEAN.Defs
import LeanRV64DLEAN.Specialization
import LeanRV64DLEAN.RiscvExtras
import RiscvDialect.ProofsPureBaseISA
-- added the imports bellow, had to move pure_func to the library folder
import LeanRV64DLEAN
import LeanRV64DLEAN.pure_func
set_option maxRecDepth 10_000
set_option maxHeartbeats 1_000_000_000
set_option match.ignoreUnusedAlts true

open Functions
open Retired
open Sail
open PureFunctions

/-
proofs: pure functions executed using the skeleton <-> untouched execution semantics in the LeanRV64DLEAN
to do: write some proof automation, tactic to do the proofs.
-/
/-
arrived at this after reverse engineering back from bit vecotr extraction
-/
def skeleton_binary  (rs2 : regidx) (rs1 : regidx) (rd : regidx) (execute_func : BitVec 64 → BitVec 64 → BitVec 64) : SailM Retired := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let result := execute_func rs1_val rs2_val
  wX_bits rd result
  pure RETIRE_SUCCESS

def skeleton_unary (rs1 : regidx) (rd : regidx) (execute_func : BitVec 64 → BitVec 64) : SailM Retired := do
  let rs1_val ← rX_bits rs1
  let result := execute_func rs1_val
  wX_bits rd result
  pure RETIRE_SUCCESS

def skeleton_UTYPE  (imm : BitVec 20) (rd : regidx) (op : uop) (execute_func : BitVec 20 → BitVec 64 → uop → BitVec 64) : SailM Retired := do
  let pc ← get_arch_pc () -- states that I modelled this model like this bc its more uniform and neat but made the proof more compilcated
  let result := execute_func imm pc op
  wX_bits rd result
  pure RETIRE_SUCCESS

-- introduced more skeletons depeending on whether pc was used or not

def skeleton_UTYPE_AUIPC  (imm : BitVec 20) (rd : regidx) (execute_func : BitVec 20 → BitVec 64 → BitVec 64) : SailM Retired := do
  let pc ← get_arch_pc (); -- TO DO READ IN THE PC , think of the effects
  let result := execute_func imm pc
  wX_bits rd result
  pure RETIRE_SUCCESS

def skeleton_UTYPE_LUI  (imm : BitVec 20) (rd : regidx) (execute_func : BitVec 20 → BitVec 64 → BitVec 64) : SailM Retired := do
  let result := execute_func imm 0#64
  wX_bits rd result
  pure RETIRE_SUCCESS


theorem add_eq (imm : BitVec 12) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ADDIW (imm) (rs1) (rd)
    = skeleton_unary rs1 rd (execute_ADDIW_pure64 imm)
  := by
  unfold Functions.execute_ADDIW skeleton_unary execute_ADDIW_pure64
  rfl

-- case destinction on the type of uop operation
theorem utype_eq_LUI (imm : (BitVec 20)) (rd : regidx):
    Functions.execute_UTYPE imm rd (uop.RISCV_LUI)
    =
    skeleton_UTYPE_LUI imm rd (fun imm1 pc => RV64.UTYPE_pure64_lui imm1 pc)
  := by
  unfold Functions.execute_UTYPE skeleton_UTYPE_LUI --execute_UTYPE_pure64
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, bind_pure_comp, pure_bind]
  unfold RV64.UTYPE_pure64_lui sign_extend Sail.BitVec.signExtend
  rfl

theorem utype_eq_AUIPC (imm : (BitVec 20)) (rd : regidx):
  Functions.execute_UTYPE imm rd (uop.RISCV_AUIPC)
    = skeleton_UTYPE_AUIPC  imm rd (fun imm pc => execute_UTYPE_pure64 imm pc uop.RISCV_AUIPC)
  := by
    unfold Functions.execute_UTYPE skeleton_UTYPE_AUIPC execute_UTYPE_pure64
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, bind_pure_comp,
      bind_map_left, BitVec.add_eq]

theorem utype_eq (imm : (BitVec 20)) (rd : regidx) (op : uop) (h_pc : s.regs.get? Register.PC = some valt):
    Functions.execute_UTYPE imm rd op s
     = skeleton_UTYPE imm rd op (execute_UTYPE_pure64) s
  := by
  unfold Functions.execute_UTYPE skeleton_UTYPE execute_UTYPE_pure64
  cases op
  ·
    simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, bind_pure_comp, pure_bind, Nat.reducePow,
      Nat.reduceMul]
    simp [get_arch_pc, readReg, PreSail.readReg, Monad.toBind, EStateM.instMonad, EStateM.map,
      EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
    cases hs : s.regs.get? Register.PC
    · rw [hs] at h_pc
      contradiction
    · simp only
      rfl
  ·
   simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, bind_pure_comp,
     bind_map_left, BitVec.add_eq]

theorem shiftiwop_eq_SLLIW (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) :
    Functions.execute_SHIFTIWOP (shamt) (rs1) (rd) (sopw.RISCV_SLLIW)
      = skeleton_unary rs1 rd (fun val1 => RV64.SHIFTIWOP_pure64_RISCV_SLLIW shamt val1)
  := by
  unfold Functions.execute_SHIFTIWOP skeleton_unary --execute_SHIFTIWOP_pure64
  rfl

theorem shiftiwop_eq_SRLIW (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) :
    Functions.execute_SHIFTIWOP (shamt) (rs1) (rd) (sopw.RISCV_SRLIW)
      = skeleton_unary rs1 rd (fun val1 => RV64.SHIFTIWOP_pure64_RISCV_SRLIW shamt val1)
  := by
  unfold Functions.execute_SHIFTIWOP skeleton_unary
  rfl

theorem shiftiwop_eq_SRAIW (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) :
    Functions.execute_SHIFTIWOP (shamt) (rs1) (rd) (sopw.RISCV_SRAIW)
      = skeleton_unary rs1 rd (fun val1 => RV64.SHIFTIWOP_pure64_RISCV_SRAIW shamt val1)
  := by
  unfold Functions.execute_SHIFTIWOP skeleton_unary
  rfl

theorem shiftiop_eq_SLLI (shamt : (BitVec 6))  (rs1 : regidx) (rd : regidx) :
    Functions.execute_SHIFTIOP (shamt) (rs1) (rd) (sop.RISCV_SLLI)
      = skeleton_unary rs1 rd (fun val1 => RV64.SHIFTIOP_pure64_RISCV_SLLI shamt val1)
  := by
  unfold Functions.execute_SHIFTIOP skeleton_unary RV64.SHIFTIOP_pure64_RISCV_SLLI shift_bits_left
  simp only [Nat.reducePow, Nat.reduceMul, BitVec.shiftLeft_eq',
    EffectKind.return_impure_toMonad_eq, bind_pure_comp, bind_map_left, BitVec.shiftLeft_eq]

theorem shiftiop_eq_SRLI (shamt : (BitVec 6))  (rs1 : regidx) (rd : regidx) :
    Functions.execute_SHIFTIOP (shamt) (rs1) (rd) (sop.RISCV_SRLI)
      = skeleton_unary rs1 rd (fun val1 => RV64.SHIFTIOP_pure64_RISCV_SRLI shamt val1)
  := by
  unfold Functions.execute_SHIFTIOP skeleton_unary RV64.SHIFTIOP_pure64_RISCV_SRLI shift_bits_right
  simp only [Nat.reducePow, Nat.reduceMul, BitVec.ushiftRight_eq',
    EffectKind.return_impure_toMonad_eq, bind_pure_comp, bind_map_left, BitVec.ushiftRight_eq]


theorem rtypew_eq_ADDW (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPEW (rs2) (rs1) (rd) (ropw.RISCV_ADDW )
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPEW_pure64_RISCV_ADDW val2 val1)
  := by -- attention_ ordering of arguements
  unfold Functions.execute_RTYPEW skeleton_binary
  rfl

theorem rtypew_eq_SUBW (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPEW (rs2) (rs1) (rd) (ropw.RISCV_SUBW )
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPEW_pure64_RISCV_SUBW val2 val1)
  := by -- attention_ ordering of arguements
  unfold Functions.execute_RTYPEW skeleton_binary
  rfl

theorem rtypew_eq_SLLW(rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPEW (rs2) (rs1) (rd) (ropw.RISCV_SLLW )
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPEW_pure64_RISCV_SLLW val2 val1)
  := by -- attention_ ordering of arguements
  unfold Functions.execute_RTYPEW skeleton_binary
  rfl

theorem rtypew_eq_SRLW(rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPEW (rs2) (rs1) (rd) (ropw.RISCV_SRLW )
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPEW_pure64_RISCV_SRLW val2 val1)
  := by -- attention_ ordering of arguements
  unfold Functions.execute_RTYPEW skeleton_binary
  rfl

theorem rtypew_eq_SRAW(rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPEW (rs2) (rs1) (rd) (ropw.RISCV_SRAW )
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPEW_pure64_RISCV_SRAW val2 val1)
  := by -- attention_ ordering of arguements
  unfold Functions.execute_RTYPEW skeleton_binary
  rfl

theorem rtype_eq_ADD (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (rop.RISCV_ADD)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPE_pure64_RISCV_ADD val2 val1)
  := by
  unfold RV64.RTYPE_pure64_RISCV_ADD Functions.execute_RTYPE skeleton_binary
  simp only [Nat.reducePow, Nat.reduceMul, EffectKind.return_impure_toMonad_eq, bind_pure_comp,
    bind_assoc, bind_map_left, BitVec.add_eq]

theorem rtype_eq_SUB (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (rop.RISCV_SUB)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPE_pure64_RISCV_SUB val2 val1)
  := by
  unfold RV64.RTYPE_pure64_RISCV_SUB Functions.execute_RTYPE skeleton_binary
  simp only [Nat.reducePow, Nat.reduceMul, EffectKind.return_impure_toMonad_eq, bind_pure_comp,
    bind_assoc, bind_map_left, BitVec.sub_eq]


theorem rtype_eq_SLL (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (rop.RISCV_SLL)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPE_pure64_RISCV_SLL val2 val1)
  := by
  unfold RV64.RTYPE_pure64_RISCV_SLL Functions.execute_RTYPE skeleton_binary
  simp
  rfl

theorem rtype_eq_SLT (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (rop.RISCV_SLT)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPE_pure64_RISCV_SLT val2 val1)
  := by
  unfold RV64.RTYPE_pure64_RISCV_SLT Functions.execute_RTYPE skeleton_binary
  simp
  rfl

theorem rtype_eq_SLTU (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (rop.RISCV_SLTU)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPE_pure64_RISCV_SLTU val2 val1)
  := by
  unfold RV64.RTYPE_pure64_RISCV_SLTU Functions.execute_RTYPE skeleton_binary zero_extend
  simp
  rfl

theorem rtype_eq_XOR (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (rop.RISCV_XOR)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPE_pure64_RISCV_XOR val1 val2)
  := by
  unfold RV64.RTYPE_pure64_RISCV_XOR Functions.execute_RTYPE skeleton_binary
  simp only [Nat.reducePow, Nat.reduceMul, EffectKind.return_impure_toMonad_eq, bind_pure_comp,
    bind_assoc, bind_map_left, BitVec.xor_eq]

theorem rtype_eq_SRL (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (rop.RISCV_SRL)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPE_pure64_RISCV_SRL val2 val1)
  := by
  unfold RV64.RTYPE_pure64_RISCV_SRL Functions.execute_RTYPE skeleton_binary
  simp
  rfl

theorem rtype_eq_SRA (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (rop.RISCV_SRA)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPE_pure64_RISCV_SRA val2 val1)
  := by
  unfold RV64.RTYPE_pure64_RISCV_SRA Functions.execute_RTYPE skeleton_binary
  simp only [Nat.reducePow, Nat.reduceMul, Nat.sub_zero, EffectKind.return_impure_toMonad_eq,
    bind_pure_comp, bind_assoc, bind_map_left, Nat.reduceAdd, BitVec.extractLsb_toNat,
    Nat.shiftRight_zero]
  rfl

theorem rtype_eq_OR (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (rop.RISCV_OR)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPE_pure64_RISCV_OR val1 val2)
  := by
  unfold RV64.RTYPE_pure64_RISCV_OR Functions.execute_RTYPE skeleton_binary
  simp only [Nat.reducePow, Nat.reduceMul, EffectKind.return_impure_toMonad_eq, bind_pure_comp,
    bind_assoc, bind_map_left, BitVec.or_eq]

theorem rtype_eq_AND (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_RTYPE (rs2) (rs1) (rd) (rop.RISCV_AND)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.RTYPE_pure64_RISCV_AND val1 val2)
  := by
  unfold RV64.RTYPE_pure64_RISCV_AND Functions.execute_RTYPE skeleton_binary
  simp only [Nat.reducePow, Nat.reduceMul, EffectKind.return_impure_toMonad_eq, bind_pure_comp,
    bind_assoc, bind_map_left, BitVec.and_eq]


theorem remw_eq_signed (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_REMW (rs2) (rs1) (rd) (true)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.REMW_pure64_signed val2 val1)
  := by
  unfold RV64.REMW_pure64_signed Functions.execute_REMW skeleton_binary sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb to_bits get_slice_int--execute_REMW_pure64
  simp only [Nat.reducePow, Nat.reduceMul, Nat.sub_zero, Nat.reduceAdd,
    EffectKind.return_impure_toMonad_eq, sail_hPow_eq, Int.reduceToNat, Int.reducePow,
    Int.reduceMul, ↓reduceIte, beq_iff_eq, Int.ofNat_toNat, bind_pure_comp, pure_bind,
    Int.ofNat_eq_coe]

theorem remw_eq_unsigned (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_REMW (rs2) (rs1) (rd) (false)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.REMW_pure64_unsigned val2 val1)
  := by
  unfold skeleton_binary RV64.REMW_pure64_unsigned Functions.execute_REMW sign_extend Sail.BitVec.signExtend to_bits get_slice_int Sail.BitVec.extractLsb
  simp
  have h (n m : Nat) : n % m = 0 ↔ (n : Int) % m = 0 := by
    omega
  simp only [h, Nat.cast_ofNat]



theorem rem_eq_unsigned (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_REM (rs2) (rs1) (rd) (false)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.REM_pure64_unsigned val2 val1)
  := by
  unfold Functions.execute_REM skeleton_binary RV64.REM_pure64_unsigned to_bits get_slice_int--execute_REM_pure64
  simp
  rfl

theorem rem_eq_signed (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_REM (rs2) (rs1) (rd) (true)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.REM_pure64_signed val2 val1)
  := by
  unfold Functions.execute_REM skeleton_binary RV64.REM_pure64_signed to_bits get_slice_int --execute_REM_pure64
  simp
  rfl

theorem mulw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_MULW (rs2) (rs1) (rd)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.MULW_pure64 val2 val1)
  := by
  unfold Functions.execute_MULW skeleton_binary
  rfl

theorem mul_eq_fff (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_MUL (rs2 ) (rs1) (rd) (mul_op := { high := False, signed_rs1:= False, signed_rs2 := False})
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.MUL_pure64_fff val2 val1)
  := by
  unfold Functions.execute_MUL skeleton_binary RV64.MUL_pure64_fff Sail.BitVec.extractLsb Functions.xlen to_bits get_slice_int --execute_MUL_pure64
  simp only [Nat.reducePow, Nat.reduceMul, decide_false, Bool.false_eq_true, ↓reduceIte,
    sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Int.reduceSub, Nat.reduceAdd,
    Int.ofNat_toNat, EffectKind.return_impure_toMonad_eq, bind_pure_comp, Int.ofNat_eq_coe,
    Int.mul_def]

theorem mul_eq_fft (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_MUL (rs2 ) (rs1) (rd) (mul_op := { high := False, signed_rs1:= False, signed_rs2 := True })
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.MUL_pure64_fft val2 val1)
  := by
  unfold Functions.execute_MUL skeleton_binary
  rfl

theorem mul_eq_ftf (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_MUL (rs2 ) (rs1) (rd) (mul_op := { high := False, signed_rs1:= True, signed_rs2 := False })
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.MUL_pure64_ftf val2 val1)
  := by
  unfold Functions.execute_MUL skeleton_binary
  rfl

theorem mul_eq_tff (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_MUL (rs2 ) (rs1) (rd) (mul_op := { high := True, signed_rs1:= False, signed_rs2 := False })
      = skeleton_binary rs2 rs1 rd (fun val1 val2 =>  RV64.MUL_pure64_tff  val2 val1)
  := by
  unfold Functions.execute_MUL skeleton_binary
  rfl

theorem mul_eq_tft (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_MUL (rs2 ) (rs1) (rd) (mul_op := { high := True, signed_rs1:= False, signed_rs2 := True })
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.MUL_pure64_tft  val2 val1)
  := by
  unfold Functions.execute_MUL skeleton_binary
  rfl

theorem mul_eq_ttf (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_MUL (rs2 ) (rs1) (rd) (mul_op := { high := True, signed_rs1:= True, signed_rs2 := False })
      = skeleton_binary rs2 rs1 rd (fun val1 val2 =>  RV64.MUL_pure64_ttf val2 val1)
  := by
  unfold Functions.execute_MUL skeleton_binary
  rfl

theorem mul_eq_ftt (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_MUL (rs2 ) (rs1) (rd) (mul_op := { high := False, signed_rs1:= True, signed_rs2 := True })
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.MUL_pure64_ftt val2 val1)
  := by
  unfold Functions.execute_MUL skeleton_binary
  rfl

theorem mul_eq_ttt (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_MUL (rs2 ) (rs1) (rd) (mul_op := { high := True, signed_rs1:= True, signed_rs2 := True })
      = skeleton_binary rs2 rs1 rd (fun val1 val2 =>  RV64.MUL_pure64_ttt val2 val1)
  := by
  unfold Functions.execute_MUL skeleton_binary
  rfl

-- here
theorem divw_eq_signed (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_DIVW (rs2 ) (rs1) (rd) true
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.DIVW_pure64_signed val2 val1)
  := by
  unfold Functions.execute_DIVW skeleton_binary sign_extend
  simp
  unfold Sail.BitVec.signExtend Sail.BitVec.extractLsb to_bits get_slice_int RV64.DIVW_pure64_signed
  simp only [Nat.reduceAdd, Int.reduceNeg, Int.ofNat_toNat, Nat.sub_zero]

--looks equivalent
theorem divw_eq_unsigned (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_DIVW (rs2 ) (rs1) (rd) false
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.DIVW_pure64_unsigned val2 val1)
  := by
  unfold Functions.execute_DIVW RV64.DIVW_pure64_unsigned skeleton_binary sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb to_bits get_slice_int
  have h (n m : Nat) : n % m = 0 ↔ (n : Int) % m = 0 := by
    omega
  simp [h]

theorem div_eq_signed (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_DIV (rs2) (rs1) (rd) true
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.DIV_pure64_signed val2 val1)
  := by
  unfold Functions.execute_DIV skeleton_binary RV64.DIV_pure64_signed
  simp
  unfold to_bits get_slice_int xlen_max_signed Functions.xlen xlen_min_signed Functions.xlen
  simp only [sail_hPow_eq, Int.reduceToNat, Int.reducePow, Int.reduceMul, Nat.reduceAdd,
    Int.reduceSub, Int.reduceNeg, zero_sub, Int.ofNat_toNat]

/-
(do
    let y ← rX_bits rs1
    let y_1 ← rX_bits rs2
    (fun a => RETIRE_SUCCESS) <$>
        wX_bits rd
          (BitVec.extractLsb' 0 64
            (BitVec.ofInt 65 ((if y_1.toNat = 0 then -1 else (↑y.toNat).tdiv ↑y_1.toNat) ⊔ 0)))) =
  do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  (fun a => RETIRE_SUCCESS) <$>
      wX_bits rd
        (BitVec.extractLsb' 0 64
          (BitVec.ofNat 65 (if rs2_val.toNat = 0 then -1 else (↑rs1_val.toNat).tdiv ↑rs2_val.toNat).toNat))
-/

theorem div_eq_unsigned (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_DIV (rs2) (rs1) (rd) false
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.DIV_pure64_unsigned val2 val1)
  := by
  unfold Functions.execute_DIV skeleton_binary  RV64.DIV_pure64_unsigned
  simp [to_bits ,Functions.xlen,  get_slice_int]
  have h (x : Int): BitVec.ofInt 65 (max x 0) = BitVec.ofNat 65 (x.toNat) := by -- potenitl new lemma ?
    cases x
    . simp only [Int.ofNat_eq_coe, Int.ofNat_zero_le, sup_of_le_left, BitVec.ofInt_natCast,
      Int.toNat_ofNat]
    . simp only [Int.negSucc_max_zero, BitVec.ofInt_ofNat, Int.toNat_negSucc]
  simp only [Int.reduceNeg, h]


theorem itype_eq_ADDI (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ITYPE (imm) (rs1) (rd) (iop.RISCV_ADDI)
      = skeleton_unary rs1 rd (fun val1 => RV64.ITYPE_pure64_RISCV_ADDI imm val1)
  := by
  unfold Functions.execute_ITYPE skeleton_unary
  simp
  rfl

theorem itype_eq_SLTI (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ITYPE (imm) (rs1) (rd) (iop.RISCV_SLTI)
      = skeleton_unary rs1 rd (fun val1 => RV64.ITYPE_pure64_RISCV_SLTI imm val1)
  := by
  unfold Functions.execute_ITYPE skeleton_unary
  simp
  rfl

theorem itype_eq_SLTIU (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ITYPE (imm) (rs1) (rd) (iop.RISCV_SLTIU)
      = skeleton_unary rs1 rd (fun val1 => RV64.ITYPE_pure64_RISCV_SLTIU imm val1)
  := by
  unfold Functions.execute_ITYPE skeleton_unary
  simp
  rfl

theorem itype_eq_ANDI (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ITYPE (imm) (rs1) (rd) (iop.RISCV_ANDI)
      = skeleton_unary rs1 rd (fun val1 => RV64.ITYPE_pure64_RISCV_ANDI imm val1)
  := by
  unfold Functions.execute_ITYPE skeleton_unary
  simp
  rfl

theorem itype_eq_ORI (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ITYPE (imm) (rs1) (rd) (iop.RISCV_ORI)
      = skeleton_unary rs1 rd (fun val1 => RV64.ITYPE_pure64_RISCV_ORI imm val1)
  := by
  unfold Functions.execute_ITYPE skeleton_unary
  simp
  rfl

theorem itype_eq_XORI (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ITYPE (imm) (rs1) (rd) (iop.RISCV_XORI)
      = skeleton_unary rs1 rd (fun val1 => RV64.ITYPE_pure64_RISCV_XORI imm val1)
  := by
  unfold Functions.execute_ITYPE skeleton_unary
  simp
  rfl


theorem zicond_rtype_eq (arg0 : regidx) (arg1 : regidx) (arg2 : regidx) :
    Functions.execute_ZICOND_RTYPE arg0 arg1 arg2 (zicondop.RISCV_CZERO_EQZ)
      = skeleton_binary arg0 arg1 arg2 (fun val1 val2 => RV64.ZICOND_RTYPE_pure64_RISCV_CZERO_EQZ  val2 val1)
  := by
  unfold Functions.execute_ZICOND_RTYPE skeleton_binary
  simp
  rfl

theorem zicond_rtype_nez (arg0 : regidx) (arg1 : regidx) (arg2 : regidx) :
    Functions.execute_ZICOND_RTYPE arg0 arg1 arg2 (zicondop.RISCV_CZERO_NEZ)
      = skeleton_binary arg0 arg1 arg2 (fun val1 val2 => RV64.ZICOND_RTYPE_pure64_RISCV_RISCV_CZERO_NEZ  val2 val1)
  := by
  unfold Functions.execute_ZICOND_RTYPE skeleton_binary
  simp
  rfl

-- here
  theorem zbs_rytpe_eq_BEXT (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ZBS_RTYPE rs2 rs1 rd brop_zbs.RISCV_BEXT
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.ZBS_RTYPE_pure64_RISCV_BEXT val2 val1)
  := by
  unfold Functions.execute_ZBS_RTYPE skeleton_binary RV64.ZBS_RTYPE_pure64_RISCV_BEXT shift_bits_left Sail.BitVec.extractLsb zero_extend Sail.BitVec.zeroExtend bool_to_bits bool_bits_forwards
  simp
  rfl

theorem zbs_rytpe_eq_BINV (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ZBS_RTYPE rs2 rs1 rd  brop_zbs.RISCV_BINV
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.ZBS_RTYPE_pure64_BINV val2 val1)
  := by
  unfold Functions.execute_ZBS_RTYPE skeleton_binary RV64.ZBS_RTYPE_pure64_BINV
  rfl


theorem zbs_rytpe_eq_BSET (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ZBS_RTYPE rs2 rs1 rd (brop_zbs.RISCV_BSET)
      = skeleton_binary rs2 rs1 rd (fun val1 val2 =>RV64.ZBS_RTYPE_pure64_RISCV_BSET val2 val1)
  := by
  unfold Functions.execute_ZBS_RTYPE skeleton_binary
  rfl


theorem zbs_iop_eq_BCLRI (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) :
    execute_ZBS_IOP (shamt ) (rs1) (rd) (biop_zbs.RISCV_BCLRI) = skeleton_unary rs1 rd (fun val1 => RV64.ZBS_IOP_pure64_RISCV_BCLRI shamt val1)
  := by
  unfold Functions.execute_ZBS_IOP skeleton_unary
  rfl

theorem zbs_iop_eq_BEXTI (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) :
    execute_ZBS_IOP (shamt ) (rs1) (rd) (biop_zbs.RISCV_BEXTI) = skeleton_unary rs1 rd (fun val1 => RV64.ZBS_IOP_pure64_RISCV_BEXTI shamt val1)
  := by
  unfold Functions.execute_ZBS_IOP skeleton_unary
  rfl


theorem zbs_iop_eq_BINVI (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx):
    execute_ZBS_IOP (shamt ) (rs1) (rd) (biop_zbs.RISCV_BINVI) = skeleton_unary rs1 rd (fun val1 => RV64.ZBS_IOP_pure64_RISCV_BINVI (shamt) (val1)) := by
  unfold Functions.execute_ZBS_IOP skeleton_unary RV64.ZBS_IOP_pure64_RISCV_BINVI
  simp
  rfl

theorem zbs_iop_eq_BSETI (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx):
    execute_ZBS_IOP (shamt ) (rs1) (rd) (biop_zbs.RISCV_BSETI) = skeleton_unary rs1 rd (fun val1 => RV64.ZBS_IOP_pure64_RISCV_BSETI shamt val1)
  := by
  unfold Functions.execute_ZBS_IOP skeleton_unary  RV64.ZBS_IOP_pure64_RISCV_BSETI
  rfl


-- to do ZBKS for crypto
theorem zbb_rtypew_eq_RORW (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ZBB_RTYPEW (rs2) (rs1) (rd) (bropw_zbb.RISCV_RORW)
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.ZBB_RTYPEW_pure64_RISCV_RORW val2 val1)
  := by
  unfold Functions.execute_ZBB_RTYPEW skeleton_binary RV64.ZBB_RTYPEW_pure64_RISCV_RORW Sail.BitVec.extractLsb rotate_bits_right sign_extend Sail.BitVec.signExtend
  simp
  unfold shift_bits_right shift_bits_left BitVec.length to_bits get_slice_int
  have h (x : BitVec 64): BitVec.setWidth 32 x = BitVec.extractLsb' 0 32 x := by rfl
  have h1 (x : BitVec 64): BitVec.setWidth 5 x = BitVec.extractLsb' 0 5 x := by rfl
  simp [h , h1]
  unfold BitVec.extractLsb
  simp only [Nat.sub_zero, Nat.reduceAdd]

theorem zbb_rtypew_eq_ROLW (rs2 : regidx) (rs1 : regidx) (rd : regidx) :
    Functions.execute_ZBB_RTYPEW (rs2) (rs1) (rd) (bropw_zbb.RISCV_ROLW)
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => RV64.ZBB_RTYPEW_pure64_RISCV_ROLW val2 val1 )
  := by
  unfold Functions.execute_ZBB_RTYPEW skeleton_binary RV64.ZBB_RTYPEW_pure64_RISCV_ROLW
  have h (x : BitVec 64): BitVec.setWidth 32 x = BitVec.extractLsb' 0 32 x := by rfl
  have h1 (x : BitVec 64): BitVec.setWidth 5 x = BitVec.extractLsb' 0 5 x := by rfl
  simp only [Nat.reducePow, Nat.reduceMul, Nat.sub_zero, Nat.reduceAdd,
    EffectKind.return_impure_toMonad_eq, sail_hPow_eq, Int.reduceToNat, Int.reducePow,
    Int.reduceMul, bind_pure_comp, pure_bind, h, BitVec.extractLsb_toNat, Nat.shiftRight_zero,
    BitVec.shiftLeft_eq, BitVec.ofInt_ofNat, BitVec.reduceExtracLsb', BitVec.sub_eq,
    BitVec.zero_sub, BitVec.toNat_neg, BitVec.ushiftRight_eq, BitVec.or_eq]
  unfold sign_extend Sail.BitVec.signExtend rotate_bits_left shift_bits_left Sail.BitVec.extractLsb BitVec.extractLsb shift_bits_right
  simp only [Nat.sub_zero, Nat.reduceAdd, BitVec.shiftLeft_eq', BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, Nat.reducePow, BitVec.ushiftRight_eq', BitVec.toNat_sub]
  unfold BitVec.length
  simp only [Nat.reducePow, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.cast_ofNat]
  unfold to_bits get_slice_int
  simp only [Nat.reduceAdd, Int.reduceToNat, Nat.cast_ofNat, BitVec.ofInt_ofNat,
    BitVec.reduceExtracLsb', BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, add_zero]

-- STOPPED BC DIDDNT YET MODELL MORE IN DIALECT

theorem zbb_extop_eq (rs1 : regidx) (rd : regidx) (op : extop_zbb)  :
    Functions.execute_ZBB_EXTOP (rs1) (rd) (op)
    = skeleton_unary rs1 rd (fun val1 => execute_ZBB_EXTOP_pure64 val1 op)
  := by
  unfold Functions.execute_ZBB_EXTOP skeleton_unary execute_ZBB_EXTOP_pure64
  rfl

theorem zba_rtypeuw_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : bropw_zba)  :
    Functions.execute_ZBA_RTYPEUW (rs2) (rs1) (rd) (op)
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_ZBA_RTYPEUW_pure64 val2 val1 op)
  := by
  unfold Functions.execute_ZBA_RTYPEUW skeleton_binary execute_ZBA_RTYPEUW_pure64
  rfl

theorem zba_rtype_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : brop_zba)  :
    Functions.execute_ZBA_RTYPE (rs2) (rs1) (rd) (op)
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_ZBA_RTYPE_pure64 val2 val1 op)
  := by
  unfold Functions.execute_ZBA_RTYPE skeleton_binary execute_ZBA_RTYPE_pure64
  rfl

theorem zbb_rtype_eq (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : brop_zbb) :
    Functions.execute_ZBB_RTYPE (rs2) (rs1) (rd) (op)
    = skeleton_binary rs2 rs1 rd (fun val1 val2 => execute_ZBB_RTYPE_pure val2 val1 op)
  := by
  unfold Functions.execute_ZBB_RTYPE skeleton_binary execute_ZBB_RTYPE_pure
  rfl

/-example :
--example proof attempt
  execute_ZBB_RTYPEW rs2 rs1 rd op = skeleton rs2 rs1 rd (execute_ZBB_RTYPEW_pure32):= by
  sorry --[TO DO ]

from pairing with alex
--theorem rX_bits_eq (rX : BitVec 5) : rX_bits rX = regval_from_reg <$> _ := by -- (readReg <| Register.ofBitVec rX) := by
  --simp [rX_bits, Functions.rX]
example execute_MUL rs2 rs1 rd mul_op  = skeleton2 rs2 rs1 (fun val1 val2 => execute_MUL_pure val1 val2 mulop ) := by
  sorry
example executeADD rs2 rs1 rd addOP = skeleton2 rs2 rs1 (λ val1 val2 . executeAddPure val1 val2 addOp)
-/
