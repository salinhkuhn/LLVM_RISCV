import SSA.Core.MLIRSyntax.EDSL
set_option maxHeartbeats 1000000000000000000

/-!
  ## Dialect semantics
  Every ISA instruction is modelled to operate on 64-bit bit vectors only.
  This should allow to gain in automation using the bv_decide.

  Additionally there is a rewrite of the function that defines the semantics in a pure BitVec operations
  version avoiding toNat and toInt, which hinders proof automation by bv_decide. (at the moment only
  for the instruction used in our lowering)
-/

namespace RV64Semantics

def ADDIW_pure64 (imm : BitVec 12) (rs1_val : BitVec 64) :  BitVec 64 :=
     BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.add (BitVec.signExtend 64 imm) rs1_val))

-- loads immediate into upper 20 bits and then fills the rest up with 0 and returns it as the result
def UTYPE_pure64_lui (imm : BitVec 20) (pc : BitVec 64) : BitVec 64 :=
     BitVec.signExtend 64 (imm ++ (0x000 : (BitVec 12)))

-- loads immediate into upper 20 bits and then fills the rest up with 0 and returns, adds the program counter and then returns it as a result
def UTYPE_pure64_AUIPC (imm : BitVec 20) (pc : BitVec 64)  : BitVec 64 :=
    BitVec.add (BitVec.signExtend 64 (BitVec.append imm (0x000 : (BitVec 12)))) pc

def SHIFTIWOP_pure64_RISCV_SLLIW (shamt : BitVec 5) (rs1_val : BitVec 64) : BitVec 64 :=
    BitVec.signExtend 64 (BitVec.shiftLeft (BitVec.extractLsb' 0 32 rs1_val) (shamt).toNat)

-- logical rightshift, filled with zeros x/2^s rounding down
def SHIFTIWOP_pure64_RISCV_SRLIW (shamt : BitVec 5) (rs1_val : BitVec 64) : BitVec 64 :=
    BitVec.signExtend 64 (BitVec.ushiftRight (BitVec.extractLsb' 0 32 rs1_val) (shamt).toNat)


def SHIFTIWOP_pure64_RISCV_SRAIW (shamt : BitVec 5) (rs1_val : BitVec 64) : BitVec 64
    :=
    BitVec.signExtend 64
      (BitVec.setWidth 32
       (BitVec.extractLsb
         (31 + shamt.toNat)
          shamt.toNat
          (BitVec.signExtend ((32) + shamt.toNat) (BitVec.extractLsb 31 0 rs1_val))
        )
      )

def SHIFTIOP_pure64_RISCV_SLLI (shamt : BitVec 6) (rs1_val : BitVec 64)  : BitVec 64
    := BitVec.shiftLeft rs1_val shamt.toNat

def SHIFTIOP_pure64_RISCV_SRLI (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
    BitVec.ushiftRight rs1_val shamt.toNat

-- here I didnt specify a return type bc it depends
def SHIFTIOP_pure64_RISCV_SRAI (shamt : (BitVec 6)) (rs1_val : (BitVec 64)): BitVec 64 :=
    let value := rs1_val ;
    let shift := shamt.toNat;
    BitVec.setWidth 64 (BitVec.extractLsb (63 + shift) shift (BitVec.signExtend (64 + shift) value)) -- had to this to tell lean how to hanlde the type
   -- (BitVec.extractLsb (63 + shift)  shift  (BitVec.signExtend ((64 + shift)) value) : BitVec 64)

-- simple integer operations on 32-bit word and then sign extend result to 64 bits
def RTYPEW_pure64_RISCV_ADDW (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
      let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
      let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
      BitVec.signExtend 64 (BitVec.add rs1_val32 rs2_val32)

def RTYPEW_pure64_RISCV_SUBW (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
      let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
      let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
      BitVec.signExtend 64 (BitVec.sub rs1_val32 rs2_val32)

-- can be all done by rfl
def RTYPEW_pure64_RISCV_SLLW (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
    let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
    let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
    let shamt := BitVec.extractLsb' 0 5 rs2_val32;
    BitVec.signExtend 64 (BitVec.shiftLeft rs1_val32 shamt.toNat)

-- can be all done by rfl
def RTYPEW_pure64_RISCV_SRLW (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : BitVec 64 :=
    let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
    let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
    let shamt := BitVec.extractLsb' 0 5 rs2_val32;
    BitVec.signExtend 64 (BitVec.ushiftRight rs1_val32 shamt.toNat)

def RTYPEW_pure64_RISCV_SRAW (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) :=
BitVec.signExtend 64
           (BitVec.setWidth 32
              (BitVec.extractLsb
                 (31 + rs2_val.toNat % 4294967296 % 32)
                     (rs2_val.toNat % 4294967296 % 32)
                          (BitVec.signExtend (32 + rs2_val.toNat % 4294967296 % 32)
                              (BitVec.extractLsb 31 0 rs1_val))))


def RTYPE_pure64_RISCV_ADD (rs2_val : BitVec 64) (rs1_val : BitVec 64) :BitVec 64 :=
      BitVec.add rs1_val rs2_val

def RTYPE_pure64_RISCV_SLT (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
    let b := BitVec.slt rs1_val rs2_val;
    BitVec.setWidth 64 (BitVec.ofBool b)

def RTYPE_pure64_RISCV_SLTU (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
    let b := BitVec.ult rs1_val rs2_val;
      BitVec.setWidth 64 (BitVec.ofBool b)

def RTYPE_pure64_RISCV_AND (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
      BitVec.and rs2_val rs1_val

def RTYPE_pure64_RISCV_OR(rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
      BitVec.or rs2_val rs1_val

def RTYPE_pure64_RISCV_XOR(rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
      BitVec.xor rs2_val rs1_val


def RTYPE_pure64_RISCV_SLL (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
       let shamt := (BitVec.extractLsb 5 0 rs2_val).toNat;
       BitVec.shiftLeft rs1_val shamt

def RTYPE_pure64_RISCV_SLL_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
       let shamt := (BitVec.extractLsb 5 0 rs2_val).toNat;
       BitVec.shiftLeft rs1_val shamt

-- adapt semantics in dialect
theorem RTYPE_pure64_RISCV_SLL_eq_RTYPE_pure64_RISCV_SLL_bv :
  RTYPE_pure64_RISCV_SLL = RTYPE_pure64_RISCV_SLL_bv :=
    by
    unfold RTYPE_pure64_RISCV_SLL RTYPE_pure64_RISCV_SLL_bv
    simp

-- sail version
def RTYPE_pure64_RISCV_SRL (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
      let shamt := (BitVec.extractLsb 5 0 rs2_val).toNat;
      BitVec.ushiftRight rs1_val shamt

-- bv decidabel version
def RTYPE_pure64_RISCV_SRL_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
      let shamt := (BitVec.extractLsb 5 0 rs2_val)
      rs1_val  >>> shamt

-- adapt semantics in dialect
theorem RTYPE_pure64_RISCV_SRL_eq_RTYPE_pure64_RISCV_SRL_bv  (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  RTYPE_pure64_RISCV_SRL = RTYPE_pure64_RISCV_SRL_bv :=
  by
  unfold RTYPE_pure64_RISCV_SRL RTYPE_pure64_RISCV_SRL_bv
  simp


def RTYPE_pure64_RISCV_SUB (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
    BitVec.sub rs1_val rs2_val

-- to simplify
def RTYPE_pure64_RISCV_SRA (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
BitVec.setWidth 64
      (BitVec.extractLsb
        (63 + (BitVec.extractLsb 5 0 rs2_val).toNat)
        (BitVec.extractLsb 5 0 rs2_val).toNat
        (BitVec.signExtend
          (64 + (BitVec.extractLsb 5 0 rs2_val).toNat) rs1_val))


def REMW_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64): BitVec 64 :=
 BitVec.signExtend 64
    (BitVec.extractLsb' 0 32
      (BitVec.ofInt 33
        (if (rs2_val.toNat: Int) % ↑(2 ^ 32) = 0 then (rs1_val.toNat : Int) % ↑(2 ^ 32)
        else ((rs1_val.toNat: Int) % ↑(2 ^ 32)).tmod ((rs2_val.toNat : Int) % ↑(2 ^ 32)))))

def REMW_pure64_signed (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  BitVec.signExtend 64
    (BitVec.extractLsb' 0 32
      (BitVec.ofInt (33)
        (if (BitVec.extractLsb 31 0 rs2_val).toInt = 0 then (BitVec.extractLsb 31 0 rs1_val).toInt
        else (BitVec.extractLsb 31 0 rs1_val).toInt.tmod (BitVec.extractLsb 31 0 rs2_val).toInt)))

--    PureFunctions.execute_REM_pure64 (False) rs2_val rs1_val  important to set sign bit to false
def REM_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64  :=
  BitVec.extractLsb' 0 64
    (BitVec.ofInt (65) (if (rs2_val.toNat: Int) = 0 then (rs1_val.toNat: Int)  else ((rs1_val.toNat :Int)).tmod (rs2_val.toNat : Int)))


def REM_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64  :=
    BitVec.extractLsb' 0 64
    (BitVec.ofInt (65) (if rs2_val.toInt = 0 then rs1_val.toInt else rs1_val.toInt.tmod rs2_val.toInt))


def MULW_pure64 (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  BitVec.signExtend 64
    (BitVec.extractLsb 31 0
      (BitVec.extractLsb' 0 64
        (BitVec.ofInt 65 ((BitVec.extractLsb 31 0 rs1_val).toInt * (BitVec.extractLsb 31 0 rs2_val).toInt))))

/-!
## mul operations flags
 the suffix indicates how the flags are assumed to be set.
{ high := _, signed_rs1:= _, signed_rs2 := _  }
-/
def MUL_pure64_fff (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
     BitVec.extractLsb 63 0 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toNat * rs2_val.toNat)))

def  MUL_pure64_fff_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=  rs2_val * rs1_val

theorem mul_eq_mul_pretty (rs2_val : BitVec 64) (rs1_val : BitVec 64) :  MUL_pure64_fff  (rs2_val) (rs1_val )
          = MUL_pure64_fff_bv  (rs2_val) (rs1_val ) :=
    by
    simp only  [MUL_pure64_fff,  MUL_pure64_fff_bv]
    apply BitVec.eq_of_toNat_eq
    simp only [HMul.hMul, Mul.mul]
    simp only [Nat.sub_zero, Nat.reduceAdd, Int.mul_def, BitVec.extractLsb_toNat,
      BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.reducePow, Nat.cast_ofNat,
      Nat.shiftRight_zero, Nat.reduceDvd, Nat.mod_mod_of_dvd, BitVec.mul_eq, BitVec.toNat_mul]
    congr
    norm_cast
    rw [Int.toNat_natCast]
    rw [Nat.mod_eq_of_lt]
    ac_rfl
    have aa := BitVec.isLt rs1_val
    have bb := BitVec.isLt rs2_val
    have := @Nat.mul_lt_mul'' _ _ _ _ aa bb
    simp at this
    omega


def  MUL_pure64_fft (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 63 0
    (BitVec.extractLsb' 0 128
      (BitVec.ofInt 129 (Int.ofNat (Int.mul (Int.ofNat rs1_val.toNat)  (rs2_val.toInt)).toNat)))

#check BitVec.ofInt
#check (Int.ofNat (Int.mul (BitVec.toInt 0#64) (Int.ofNat (BitVec.toNat 0#64))).toNat)

def MUL_pure64_ftf (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : BitVec 64 :=
  BitVec.extractLsb 63 0 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toInt * rs2_val.toNat)))


def MUL_pure64_tff (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toNat * rs2_val.toNat)))


def MUL_pure64_tft (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
   BitVec.extractLsb 127 64 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toNat * rs2_val.toInt)))


def MUL_pure64_ttf (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toInt * rs2_val.toNat)))

def MUL_pure64_ftt (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 63 0 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toInt * rs2_val.toInt)))

def MUL_pure64_ftt_bv  (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  rs2_val * rs1_val

-- (div n d) * d + mod n d = n
-- (n / d) * d + n % d = n

-- ediv/emod
--  n e% d =defn = smallest non-negative number that is congruent to n modulo d.
--  10 e% 3 =defn= {-5, -2, [1], 4, 7, 10, 13, 16}
--  11 e% 3 =defn= {-4, -1, [2], 5, 8, 11, 13, 16}
-- n e/ d =defm= k where ∃! k, k * d +  n e% d = n

-- bdiv/bmod
-- n b% d = smallest number (in absolute value) that is congruent to n modulo d.
--  10 e% 3 =defn= {-5, -2, [1], 4, 7, 10, 13, 16}
--  11 e% 3 =defn= {-4, [-1], 2, 5, 8, 11, 13, 16}
-- n b/ d =defm= k where ∃! k, k * d +  n e% d = n

-- tdiv/tmod
-- n t/ d =defn= (truncating?) division, rounding toward zero.
-- 3 t/ 5 = 0
-- -2 t/ 5 = 0
-- n t%d =defn= whatever makes the euclid's equation work/


-- fdiv/fmod:
-- n f/ d =defn= floor division, round toward -∞
-- 3 f/ 5 = 0
-- -2 f/ 5 = -1


-- binary string: 1111
-- unsigned:      15
-- signed  :     -1 = 15 b% 16
--

-- tdiv/tmod
-- fdiv/fmod


theorem BitVec.ofInt_toInt_eq_signExtend {w w' : Nat} {x : BitVec w} : BitVec.ofInt w' x.toInt = x.signExtend w' := by
  apply BitVec.eq_of_toInt_eq
  by_cases hw' : w' ≤ w
  · simp; rw [BitVec.toInt_signExtend_eq_toInt_bmod_of_le _ hw']
  · simp at hw'
    rw [BitVec.toInt_ofInt]
    rw [BitVec.toInt_signExtend_of_le (by omega)]
    have hxlt := @BitVec.two_mul_toInt_lt w x
    have hxle := @BitVec.le_two_mul_toInt w x
    have : 2^w < 2^w' := by apply Nat.pow_lt_pow_of_lt (by simp) (by assumption)
    have : - 2^w' < - 2^w := by
      apply Int.neg_lt_neg
      norm_cast
    rw [Int.bmod_eq_of_le_mul_two] <;> push_cast <;> omega

-- to do
theorem toInt_toInt_ofInt_eq_toNat_toNat_ofNa{w w' : Nat }{x y : BitVec w } (h : w' ≤ w):
    BitVec.ofNat w' (x.toNat * y.toNat) = BitVec.ofInt w' (x.toInt * y.toInt) := by
  rw [BitVec.ofNat_mul]
  simp
  rw [BitVec.ofInt_mul]
  rw [BitVec.ofInt_toInt_eq_signExtend]
  rw [BitVec.ofInt_toInt_eq_signExtend]
  rw [BitVec.signExtend_eq_setWidth_of_le _ (by omega)]
  rw [BitVec.signExtend_eq_setWidth_of_le _ (by omega)]


theorem t_toInt_ofInt_eq_toNat_toNat_ofNa{w w' : Nat } { x y : BitVec w } : BitVec.ofInt w' (x.toInt * y.toNat)
  = BitVec.ofNat  w' (x.toNat * y.toNat) := by
    simp only [HMul.hMul, Mul.mul]
    sorry

theorem toInt_ofInt_toNat_ofNat {w : Nat } {x : BitVec w} : BitVec.ofInt w (x.toInt) =  BitVec.ofNat w (x.toNat)
  := by simp


theorem toInt_toInt_eq_toInt (w : Nat) (x y : BitVec w) : BitVec.ofInt w (x.toInt *  y.toInt) = BitVec.ofInt w (x * y).toInt :=
  by
  simp only [BitVec.toInt_mul]
  simp only [HMul.hMul, Mul.mul]
  apply BitVec.eq_of_toInt_eq
  simp

#print axioms toInt_toInt_eq_toInt

-- #check Nat.mod_mod_eq_mod_of_lt_right

-- theorem BitVec.extractLsb'_extractLsb'_eq_extractLsb'_of_lt {x : BitVec w}

/-- An `extractLsb`' starting from `0` is the same as `setWidth`. -/
@[simp]
theorem extractLsb'_eq_setWidth {x : BitVec w} : x.extractLsb' 0 n = x.setWidth n := by
  ext i hi
  simp?


theorem extractLsb'_ofInt_eq_ofInt {x : Nat } {w w' : Nat}  {h : w ≤ w'} :
    (BitVec.extractLsb' 0 w (BitVec.ofInt w' x)) = (BitVec.ofInt w x) := by
  simp only [BitVec.ofInt_natCast, extractLsb'_eq_setWidth]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  apply Nat.mod_mod_of_dvd _ (by exact Nat.pow_dvd_pow_iff_le_right'.mpr h)



theorem BitVec.setWidth_signExtend_eq_self {w w' : Nat} {x : BitVec w} (h : w ≤ w') : (x.signExtend w').setWidth w = x := by
  ext i hi
  simp [hi, BitVec.getLsbD_signExtend]
  omega

-- to do
theorem mul_eq_mul_ftt_pretty (rs2_val : BitVec 64) (rs1_val : BitVec 64) :  MUL_pure64_ftt  (rs2_val) (rs1_val )
     = MUL_pure64_ftt_bv  (rs2_val) (rs1_val ) :=
  by
  unfold  MUL_pure64_ftt  MUL_pure64_ftt_bv
  rw [BitVec.extractLsb]
  simp
  have : rs1_val.toInt = (rs1_val.signExtend 129).toInt := by
    simp [BitVec.toInt_signExtend_of_le]
  simp only [this]
  have : rs2_val.toInt = (rs2_val.signExtend 129).toInt := by
    simp [BitVec.toInt_signExtend_of_le]
  simp only [this]
  rw [BitVec.ofInt_mul]
  simp
  rw [BitVec.setWidth_mul _ _ (by omega)]
  rw [BitVec.setWidth_signExtend_eq_self (by simp),BitVec.setWidth_signExtend_eq_self (by simp)]
  ac_nf

theorem mul_eq_mul_ftt_pretty' (rs2_val : BitVec 64) (rs1_val : BitVec 64) :  MUL_pure64_ftt  (rs2_val) (rs1_val )
     = MUL_pure64_ftt_bv  (rs2_val) (rs1_val ) := by



theorem extractLsb_extractLsb'_ofInt  {rs1_val : Int }: (BitVec.extractLsb 63 0
  (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val)))) =
    (BitVec.ofInt 64 (rs1_val)) := sorry



/-
(BitVec.extractLsb 63 0 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toInt * rs2_val.toInt))))
-/


def MUL_pure64_ttt (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toInt * rs2_val.toInt)))

def DIVW_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64
    (BitVec.extractLsb' 0 32
      (BitVec.ofInt 33
        (if
            2147483647 <
              if (BitVec.extractLsb 31 0 rs2_val).toInt = 0 then -1
              else (BitVec.extractLsb 31 0 rs1_val).toInt.tdiv (BitVec.extractLsb 31 0 rs2_val).toInt then
          -2147483648
        else
          if (BitVec.extractLsb 31 0 rs2_val).toInt = 0 then -1
          else (BitVec.extractLsb 31 0 rs1_val).toInt.tdiv (BitVec.extractLsb 31 0 rs2_val).toInt)))

def  DIVW_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
       BitVec.signExtend 64
    (BitVec.extractLsb' 0 32
      (BitVec.ofInt 33
        (if (rs2_val.toNat: Int)  % 4294967296 = 0 then -1
        else ((rs1_val.toNat : Int) % 4294967296).tdiv ((rs2_val.toNat : Int) % 4294967296))))


-- TO DO
def DIV_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb' 0 64
    (BitVec.ofInt 65
      (if 9223372036854775807 < if rs2_val.toInt = 0 then -1 else rs1_val.toInt.tdiv rs2_val.toInt then
        -9223372036854775808
      else if rs2_val.toInt = 0 then -1 else rs1_val.toInt.tdiv rs2_val.toInt))

-- TO DO
def DIV_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb' 0 64 (BitVec.ofInt 65 (if ((rs2_val.toNat):Int) = 0 then -1 else (rs1_val.toNat : Int).tdiv (rs2_val.toNat: Int)))

def ITYPE_pure64_RISCV_ADDI (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
    let immext : BitVec 64 := (BitVec.signExtend 64 imm) ;
    BitVec.add rs1_val immext

def ITYPE_pure64_RISCV_SLTI (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
       let immext : BitVec 64 := (BitVec.signExtend 64 imm);
       let b := BitVec.slt rs1_val immext;
       BitVec.zeroExtend 64 (BitVec.ofBool b)

def ITYPE_pure64_RISCV_SLTIU (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
       let immext : BitVec 64 := (BitVec.signExtend 64 imm);
       let b := BitVec.ult rs1_val immext;
       BitVec.setWidth 64 (BitVec.ofBool b)

def  ITYPE_pure64_RISCV_ANDI (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
    let immext : BitVec 64 := (BitVec.signExtend 64 imm);
      BitVec.and rs1_val immext

def ITYPE_pure64_RISCV_ORI (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
      let immext : BitVec 64 := (BitVec.signExtend 64 imm) ;
      BitVec.or rs1_val immext


def  ITYPE_pure64_RISCV_XORI (imm : (BitVec 12)) (rs1_val : (BitVec 64)) : BitVec 64 :=
      let immext : BitVec 64 := (BitVec.signExtend 64 imm) ;
      BitVec.xor rs1_val immext

def ZICOND_RTYPE_pure64_RISCV_CZERO_EQZ (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) :=
      (if rs2_val = BitVec.zero 64 then BitVec.zero 64 else rs1_val)

def ZICOND_RTYPE_pure64_RISCV_RISCV_CZERO_NEZ (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) :=
   (if rs2_val = BitVec.zero 64 then rs1_val else BitVec.zero 64)


def ZBS_RTYPE_pure64_RISCV_BCLR (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.and rs1_val (BitVec.not (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) (BitVec.extractLsb  5 0 rs2_val).toNat))


def ZBB_EXTOP_pure64_RISCV_SEXTB (rs1_val : BitVec 64) :=
  BitVec.signExtend 64 (BitVec.extractLsb 7 0 rs1_val)

def ZBB_EXTOP_pure64_RISCV_SEXTH  (rs1_val : BitVec 64) :=
  BitVec.signExtend 64 (BitVec.extractLsb 15 0 rs1_val)

def ZBB_EXTOP_pure64_RISCV_ZEXTH  (rs1_val : BitVec 64) :=
  BitVec.zeroExtend 64 (BitVec.extractLsb 15 0 rs1_val)

def ZBS_RTYPE_pure64_RISCV_BEXT (rs2_val : BitVec 64) (rs1_val : BitVec 64)  :=
  BitVec.setWidth 64
    (match
      BitVec.and rs1_val (BitVec.shiftLeft (BitVec.setWidth 64 1#1) (BitVec.extractLsb 5 0 rs2_val).toNat) !=
        0#64 with
    | true => 1#1
    | false => 0#1)

 def ZBS_RTYPE_pure64_BINV (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.xor rs1_val  (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) (BitVec.extractLsb 5 0 rs2_val).toNat)

def ZBS_RTYPE_pure64_RISCV_BSET (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.or rs1_val (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) (BitVec.extractLsb 5 0 rs2_val).toNat)

def ZBS_IOP_pure64_RISCV_BCLRI (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.and rs1_val (BitVec.not (BitVec.shiftLeft (BitVec.setWidth 64 1#1) (shamt.toNat)))

def ZBS_IOP_pure64_RISCV_BEXTI (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.setWidth 64
      (match (BitVec.and (rs1_val) (BitVec.shiftLeft (BitVec.setWidth 64 1#1) shamt.toNat)) != 0#64 with
      | true => 1#1
      | false => 0#1)

def ZBS_IOP_pure64_RISCV_BINVI (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.xor rs1_val  (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) shamt.toNat)

def ZBS_IOP_pure64_RISCV_BSETI (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.or rs1_val (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) shamt.toNat)

def ZBB_RTYPEW_pure64_RISCV_RORW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.signExtend (64)
      (BitVec.or (BitVec.ushiftRight (BitVec.setWidth 32 rs1_val) (rs2_val.toNat % 32))
        (BitVec.shiftLeft (BitVec.setWidth 32 rs1_val)
          ((2 ^ 5 - rs2_val.toNat % 32 +
              32 % 2 ^ (5 + 1)) %
            2 ^ 5)))

def ZBB_RTYPEW_pure64_RISCV_ROLW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
BitVec.signExtend 64
    (BitVec.or (BitVec.shiftLeft (BitVec.setWidth 32 rs1_val) (BitVec.extractLsb 4 0 rs2_val).toNat)
      (BitVec.ushiftRight (BitVec.setWidth 32 rs1_val) (
        ((BitVec.sub ((BitVec.extractLsb' 0 (5)
            (BitVec.ofInt (6)
              (32))))
          (BitVec.extractLsb 4 0 rs2_val)))).toNat))

 def ZBB_RTYPE_pure64_RISCV_ROL (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.or (BitVec.shiftLeft  rs1_val (BitVec.extractLsb 5 0 rs2_val).toNat)
    (BitVec.ushiftRight rs1_val  (BitVec.extractLsb' 0 6 (BitVec.ofInt (7) (64)) - BitVec.extractLsb 5 0 rs2_val).toNat)

 def ZBB_RTYPE_pure64_RISCV_ROR (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
      BitVec.or (BitVec.ushiftRight rs1_val (BitVec.extractLsb 5 0 rs2_val).toNat)
    (BitVec.shiftLeft rs1_val ((BitVec.extractLsb' 0 6 (BitVec.ofInt (7) (64)) - BitVec.extractLsb 5 0 rs2_val)).toNat)

 def ZBA_RTYPEUW_pure64_RISCV_ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
      BitVec.zeroExtend 64 (BitVec.extractLsb 31 0 rs1_val) <<< 0#2 + rs2_val


def  ZBA_RTYPEUW_pure64_RISCV_SH1ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
    BitVec.add (BitVec.zeroExtend (Int.toNat 64) (BitVec.extractLsb 31 0 rs1_val) <<< 1#2)  (rs2_val)

def ZBA_RTYPEUW_pure64_RISCV_SH2ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
      BitVec.add (BitVec.zeroExtend (Int.toNat 64) (BitVec.extractLsb 31 0 rs1_val) <<< 2#2) rs2_val

def  ZBA_RTYPEUW_pure64_RISCV_SH3ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
      BitVec.add (BitVec.zeroExtend (Int.toNat 64) (BitVec.extractLsb 31 0 rs1_val) <<< 3#2)  rs2_val

def ZBA_RTYPE_pure64_RISCV_SH1ADD (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
    BitVec.add (rs1_val <<< 1#2) rs2_val

def ZBA_RTYPE_pure64_RISCV_SH2ADD (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
    BitVec.add (rs1_val <<< 2#2) rs2_val

def ZBA_RTYPE_pure64_RISCV_SH3ADD(rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
    BitVec.add (rs1_val <<< 3#2) rs2_val

/-
to complete in the future:
def ZBB_RYTPE_pure64_RISCV_ + rytpe from sail side is missing.
|pack
|packh
slli.uw

 -/

end RV64Semantics
