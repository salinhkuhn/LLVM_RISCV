import SSA.Core.MLIRSyntax.EDSL
set_option maxHeartbeats 1000000000000000000

/-!
  ## Dialect semantics bit-vectorization
This file contains the `RV64` instruction semantics in a form that does not contain BitVec.toInt and BitVec.toNat.
ToInt/ToNat calls hinder proof automation by bv_decide.
To guarantee faithful rewrites of the dialect semantics as defined in Sail-Lean, this file also contains
a proof for each rewrite.
The instruction semantics suffixed by "bv" indicates that it is a transformed defintion where we removed
toInt/toNat calls.
-/

/-  ## Additional introducded lemmas on bit vectors -/
namespace pure_semantics
theorem sshiftRight_eq_sshiftRight_extractLsb {w : Nat}
    {lw : Nat} (hll : 2^lw = w) (hlw : lw > 0 )
    (x y : BitVec w)(h : BitVec.toNat y < 2^lw ) : x.sshiftRight y.toNat = x.sshiftRight (y.extractLsb (lw - 1) 0).toNat := by
    apply BitVec.eq_of_toNat_eq
    simp
    suffices y.toNat = (y.toNat % 2 ^ (lw - 1 + 1)) by
      rw [← this ]
    have : (lw - 1 + 1) = lw := by omega
    rw [this, hll]
    rw [Nat.mod_eq_of_lt]
    rw [hll] at h
    exact h

theorem eq_of_toNat_eq3 {n} : ∀ {x y : BitVec n}, x.toNat = y.toNat → x = y
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem sshiftRight_eq_setWidth_extractLsb_signExtend {w : Nat} (n : Nat) (x : BitVec w) :
    x.sshiftRight n =
    ((x.signExtend (w + n)).extractLsb (w - 1 + n) n).setWidth w := by
  ext i hi
  simp [BitVec.getElem_sshiftRight]
  simp [show i ≤ w - 1 by omega]
  simp [BitVec.getLsbD_signExtend]
  by_cases hni : (n + i) < w <;> simp [hni] <;> omega

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

theorem toInt_toInt_ofInt_eq_toNat_toNat_ofNa{w w' : Nat }{x y : BitVec w } (h : w' ≤ w):
    BitVec.ofNat w' (x.toNat * y.toNat) = BitVec.ofInt w' (x.toInt * y.toInt) := by
  rw [BitVec.ofNat_mul]
  simp
  rw [BitVec.ofInt_mul]
  rw [BitVec.ofInt_toInt_eq_signExtend]
  rw [BitVec.ofInt_toInt_eq_signExtend]
  rw [BitVec.signExtend_eq_setWidth_of_le _ (by omega)]
  rw [BitVec.signExtend_eq_setWidth_of_le _ (by omega)]

theorem neg_ofNat_eq_ofInt_neg {w : Nat} (x : Nat) :
    - BitVec.ofNat w x = BitVec.ofInt w (- x) := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_neg, BitVec.toInt_ofNat]

@[simp]
theorem extractLsb'_eq_setWidth {x : BitVec w} : x.extractLsb' 0 n = x.setWidth n := by
  ext i hi
  simp?

theorem extractLsb'_ofInt_eq_ofInt {x : Int} {w w' : Nat}  {h : w ≤ w'} :
    (BitVec.extractLsb' 0 w (BitVec.ofInt w' x)) = (BitVec.ofInt w x) := by
  simp only [extractLsb'_eq_setWidth]
  rw [← BitVec.signExtend_eq_setWidth_of_le _ (by omega)]
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_signExtend, BitVec.toInt_ofInt, h, inf_of_le_left]
  rw [Int.bmod_bmod_of_dvd]
  apply Nat.pow_dvd_pow 2 h

theorem extractLsb'_ofInt_eq_ofInt_ofNat {x : Nat} {w w' : Nat}  {h : w ≤ w'} :
    (BitVec.extractLsb' 0 w (BitVec.ofInt w' x)) = (BitVec.ofInt w x) := by
  apply extractLsb'_ofInt_eq_ofInt
  exact h

theorem BitVec.setWidth_signExtend_eq_self {w w' : Nat} {x : BitVec w} (h : w ≤ w') : (x.signExtend w').setWidth w = x := by
  ext i hi
  simp  [hi, BitVec.getLsbD_signExtend]
  omega


def ADDIW_pure64 (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
     BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.add (BitVec.signExtend 64 imm) rs1_val))

def UTYPE_pure64_lui (imm : BitVec 20) (pc : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (imm ++ (0x000 : (BitVec 12)))

def UTYPE_pure64_AUIPC (imm : BitVec 20) (pc : BitVec 64) : BitVec 64 :=
  BitVec.add (BitVec.signExtend 64 (BitVec.append imm (0x000 : (BitVec 12)))) pc

def SHIFTIWOP_pure64_RISCV_SLLIW (shamt : BitVec 5) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.shiftLeft (BitVec.extractLsb' 0 32 rs1_val) (shamt).toNat)

def SHIFTIWOP_pure64_RISCV_SLLIW_bv (shamt : BitVec 5) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 ( (BitVec.extractLsb' 0 32 rs1_val)  <<< (shamt))

theorem SHIFTIWOP_pure64_RISCV_SLLIW_eq_SHIFTIWOP_pure64_RISCV_SLLIW_bv (shamt : BitVec 5) (rs1_val : BitVec 64) :
  SHIFTIWOP_pure64_RISCV_SLLIW (shamt ) (rs1_val ) = SHIFTIWOP_pure64_RISCV_SLLIW_bv (shamt) (rs1_val) :=
  by
  unfold SHIFTIWOP_pure64_RISCV_SLLIW SHIFTIWOP_pure64_RISCV_SLLIW_bv
  rfl

def SHIFTIWOP_pure64_RISCV_SRLIW (shamt : BitVec 5) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.ushiftRight (BitVec.extractLsb' 0 32 rs1_val) (shamt).toNat)

def SHIFTIWOP_pure64_RISCV_SRLIW_bv (shamt : BitVec 5) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 ( (BitVec.extractLsb' 0 32 rs1_val) >>> (shamt))

theorem  SHIFTIWOP_pure64_RISCV_SRLIW_eq_SHIFTIWOP_pure64_RISCV_SRLIW_bv (shamt : BitVec 5) (rs1_val : BitVec 64) :
  SHIFTIWOP_pure64_RISCV_SRLIW (shamt) (rs1_val) =  SHIFTIWOP_pure64_RISCV_SRLIW_bv (shamt) (rs1_val) :=
  by
  unfold SHIFTIWOP_pure64_RISCV_SRLIW SHIFTIWOP_pure64_RISCV_SRLIW_bv
  rfl

def SHIFTIWOP_pure64_RISCV_SRAIW (shamt : BitVec 5) (rs1_val : BitVec 64) : BitVec 64 :=
    BitVec.signExtend 64
      (BitVec.setWidth 32
       (BitVec.extractLsb
         (31 + shamt.toNat)
          shamt.toNat
          (BitVec.signExtend ((32) + shamt.toNat) (BitVec.extractLsb 31 0 rs1_val))))

def SHIFTIWOP_pure64_RISCV_SRAIW_bv (shamt : BitVec 5) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.sshiftRight' (BitVec.extractLsb 31 0 rs1_val) shamt)

theorem SHIFTIWOP_pure64_RISCV_SRAIW_eq_SHIFTIWOP_pure64_RISCV_SRAIW_bv (shamt : BitVec 5) (rs1_val : BitVec 64) :
  SHIFTIWOP_pure64_RISCV_SRAIW (shamt) (rs1_val) = SHIFTIWOP_pure64_RISCV_SRAIW_bv (shamt) (rs1_val) :=
  by
  unfold SHIFTIWOP_pure64_RISCV_SRAIW SHIFTIWOP_pure64_RISCV_SRAIW_bv
  rw [← sshiftRight_eq_setWidth_extractLsb_signExtend]
  rfl

def SHIFTIOP_pure64_RISCV_SLLI (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.shiftLeft rs1_val shamt.toNat

def  SHIFTIOP_pure64_RISCV_SLLI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  rs1_val <<< shamt

theorem SHIFTIOP_pure64_RISCV_SLLI_eq_SHIFTIOP_pure64_RISCV_SLLI_bv :
  SHIFTIOP_pure64_RISCV_SLLI (shamt) (rs1_val) = SHIFTIOP_pure64_RISCV_SLLI_bv (shamt) (rs1_val) := by
  unfold SHIFTIOP_pure64_RISCV_SLLI SHIFTIOP_pure64_RISCV_SLLI_bv
  simp

def SHIFTIOP_pure64_RISCV_SRLI (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.ushiftRight rs1_val shamt.toNat

def SHIFTIOP_pure64_RISCV_SRLI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) : BitVec 64 :=
  rs1_val >>> shamt

theorem SHIFTIOP_pure64_RISCV_SRLI_eq_SHIFTIOP_pure64_RISCV_SRLI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) :
  SHIFTIOP_pure64_RISCV_SRLI (shamt) (rs1_val) = SHIFTIOP_pure64_RISCV_SRLI_bv (shamt) (rs1_val) := by
  unfold SHIFTIOP_pure64_RISCV_SRLI SHIFTIOP_pure64_RISCV_SRLI_bv
  simp

def SHIFTIOP_pure64_RISCV_SRAI (shamt : BitVec 6) (rs1_val : BitVec 64): BitVec 64 :=
  let value := rs1_val ;
  let shift := shamt.toNat;
  BitVec.setWidth 64 (BitVec.extractLsb (63 + shift) shift (BitVec.signExtend (64 + shift) value))

def SHIFTIOP_pure64_RISCV_SRAI_bv (shamt : BitVec 6) (rs1_val : BitVec 64): BitVec 64 :=
  BitVec.sshiftRight' rs1_val  shamt

theorem SHIFTIOP_pure64_RISCV_SRAI_eq_SHIFTIOP_pure64_RISCV_SRAI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) :
  SHIFTIOP_pure64_RISCV_SRAI (shamt) (rs1_val ) = SHIFTIOP_pure64_RISCV_SRAI_bv (shamt) (rs1_val ) :=
  by
  unfold SHIFTIOP_pure64_RISCV_SRAI SHIFTIOP_pure64_RISCV_SRAI_bv
  simp
  rw [sshiftRight_eq_setWidth_extractLsb_signExtend]

def RTYPEW_pure64_RISCV_ADDW (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
  let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
  BitVec.signExtend 64 (BitVec.add rs1_val32 rs2_val32)

def RTYPEW_pure64_RISCV_SUBW (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
  let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
  BitVec.signExtend 64 (BitVec.sub rs1_val32 rs2_val32)

def RTYPEW_pure64_RISCV_SLLW (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
  let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
  let shamt := BitVec.extractLsb' 0 5 rs2_val32;
  BitVec.signExtend 64 (BitVec.shiftLeft rs1_val32 shamt.toNat)

def RTYPEW_pure64_RISCV_SLLW_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
  let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
  let shamt := BitVec.extractLsb' 0 5 rs2_val32;
  BitVec.signExtend 64 (rs1_val32 <<< shamt)

theorem  RTYPEW_pure64_RISCV_SLLW_eq_RTYPEW_pure64_RISCV_SLLW_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  RTYPEW_pure64_RISCV_SLLW (rs2_val) (rs1_val) =  RTYPEW_pure64_RISCV_SLLW_bv (rs2_val) (rs1_val) :=
  by
  unfold RTYPEW_pure64_RISCV_SLLW RTYPEW_pure64_RISCV_SLLW_bv
  simp only [extractLsb'_eq_setWidth, Nat.reduceLeDiff, BitVec.setWidth_setWidth_of_le,
    BitVec.toNat_setWidth, Nat.reducePow, BitVec.shiftLeft_eq, BitVec.shiftLeft_eq']

def RTYPEW_pure64_RISCV_SRLW (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
  let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
  let shamt := BitVec.extractLsb' 0 5 rs2_val32;
  BitVec.signExtend 64 (BitVec.ushiftRight rs1_val32 shamt.toNat)

def RTYPEW_pure64_RISCV_SRLW_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := BitVec.extractLsb' 0 32 rs1_val;
  let rs2_val32 := BitVec.extractLsb' 0 32 rs2_val;
  let shamt := BitVec.extractLsb' 0 5 rs2_val32;
  BitVec.signExtend 64 (rs1_val32 >>> shamt)

theorem RTYPEW_pure64_RISCV_SLLW_eq_RTYPEW_pure64_RISCV_SRLW_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  RTYPEW_pure64_RISCV_SRLW (rs2_val) (rs1_val) =  RTYPEW_pure64_RISCV_SRLW_bv (rs2_val) (rs1_val) := by
  unfold RTYPEW_pure64_RISCV_SRLW RTYPEW_pure64_RISCV_SRLW_bv
  simp

def RTYPEW_pure64_RISCV_SRAW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.signExtend 64
           (BitVec.setWidth 32
              (BitVec.extractLsb
                 (31 + rs2_val.toNat % 4294967296 % 32)
                     (rs2_val.toNat % 4294967296 % 32)
                          (BitVec.signExtend (32 + rs2_val.toNat % 4294967296 % 32)
                              (BitVec.extractLsb 31 0 rs1_val))))

def RTYPEW_pure64_RISCV_SRAW_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.signExtend 64
  (BitVec.sshiftRight' (BitVec.extractLsb 31 0 rs1_val)  (BitVec.extractLsb 4 0 rs2_val))

theorem RTYPEW_pure64_RISCV_SRAW_eq_RTYPEW_pure64_RISCV_SRAW_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  RTYPEW_pure64_RISCV_SRAW (rs2_val) (rs1_val) = RTYPEW_pure64_RISCV_SRAW_bv (rs2_val) (rs1_val) :=
  by
  unfold RTYPEW_pure64_RISCV_SRAW RTYPEW_pure64_RISCV_SRAW_bv
  rw [← sshiftRight_eq_setWidth_extractLsb_signExtend]
  simp

def RTYPE_pure64_RISCV_ADD (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
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
  let shamt := (BitVec.extractLsb 5 0 rs2_val);
  rs1_val <<< shamt

theorem RTYPE_pure64_RISCV_SLL_eq_RTYPE_pure64_RISCV_SLL_bv  (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  RTYPE_pure64_RISCV_SLL (rs2_val) (rs1_val)= RTYPE_pure64_RISCV_SLL_bv (rs2_val) (rs1_val) := by
  unfold RTYPE_pure64_RISCV_SLL  RTYPE_pure64_RISCV_SLL_bv
  simp

def RTYPE_pure64_RISCV_SRL (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let shamt := (BitVec.extractLsb 5 0 rs2_val).toNat;
  BitVec.ushiftRight rs1_val shamt

def RTYPE_pure64_RISCV_SRL_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let shamt := (BitVec.extractLsb 5 0 rs2_val)
  rs1_val >>> shamt

theorem RTYPE_pure64_RISCV_SRL_eq_RTYPE_pure64_RISCV_SRL_bv  (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  RTYPE_pure64_RISCV_SRL (rs2_val) (rs1_val) = RTYPE_pure64_RISCV_SRL_bv (rs2_val) (rs1_val) :=
  by
  unfold RTYPE_pure64_RISCV_SRL RTYPE_pure64_RISCV_SRL_bv
  simp

def RTYPE_pure64_RISCV_SUB (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.sub rs1_val rs2_val

def RTYPE_pure64_RISCV_SRA (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.setWidth 64
      (BitVec.extractLsb
        (63 + (BitVec.extractLsb 5 0 rs2_val).toNat)
        (BitVec.extractLsb 5 0 rs2_val).toNat
        (BitVec.signExtend
          (64 + (BitVec.extractLsb 5 0 rs2_val).toNat) rs1_val))

def RTYPE_pure64_RISCV_SRA_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.sshiftRight' rs1_val (BitVec.extractLsb 5 0 rs2_val)

theorem RTYPE_pure64_RISCV_SRA_eqRTYPE_pure64_RISCV_SRA_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  RTYPE_pure64_RISCV_SRA  (rs2_val) (rs1_val) = RTYPE_pure64_RISCV_SRA_bv (rs2_val) (rs1_val) := by
  unfold RTYPE_pure64_RISCV_SRA RTYPE_pure64_RISCV_SRA_bv
  rw [BitVec.sshiftRight']
  rw [sshiftRight_eq_setWidth_extractLsb_signExtend]

def REMW_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64): BitVec 64 :=
 BitVec.signExtend 64
    (BitVec.extractLsb' 0 32
      (BitVec.ofInt 33
        (if ((BitVec.extractLsb 31 0 rs2_val).toNat : Int) = 0 then ↑(BitVec.extractLsb 31 0 rs1_val).toNat
        else ((BitVec.extractLsb 31 0 rs1_val).toNat : Int).tmod ↑(BitVec.extractLsb 31 0 rs2_val).toNat)))

def REMW_pure64_unsigned_bv (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  BitVec.signExtend 64
      ((BitVec.extractLsb 31 0 rs1_val).umod (BitVec.extractLsb 31 0 rs2_val))

theorem REMW_pure64_unsigned_eq_REMW_pure64_unsigned_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  REMW_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) =  REMW_pure64_unsigned_bv (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) :=
  by
  unfold  REMW_pure64_unsigned REMW_pure64_unsigned_bv
  rw [extractLsb'_ofInt_eq_ofInt (h:= by simp)]
  split
  case isTrue ht =>
      congr
      rw [BitVec.extractLsb,BitVec.extractLsb]
      simp only [Nat.sub_zero, Nat.reduceAdd]
      rw [BitVec.extractLsb] at ht
      simp only [extractLsb'_eq_setWidth]
      simp only [Nat.sub_zero, Nat.reduceAdd] at ht
      norm_cast at ht
      obtain h : (BitVec.extractLsb' 0 32 rs2_val) = 0#_ :=
        BitVec.eq_of_toNat_eq ht
      obtain h1 : (0#32).toNat = 0 := by bv_decide
      simp only [BitVec.toNat_setWidth, Int.natCast_emod, Int.natCast_pow, Nat.cast_ofNat,
        BitVec.umod_eq]
      rw [show 0 = (0#32).toNat by omega, ← BitVec.toNat_eq] at ht
      conv at ht =>
        lhs
        rw [show (0#32).toNat = 0 by omega]
      rw [← BitVec.setWidth_eq_extractLsb' (by simp)] at ht
      rw [ht]
      rw [BitVec.umod_zero]
      rw [← BitVec.toInt_inj]
      simp only [Int.reducePow, BitVec.toInt_ofInt, Nat.reducePow, BitVec.toInt_setWidth]
      have helper : ((4294967296 : Nat) : Int) = (4294967296 : Int) := rfl
      rw [← helper]
      rw [Int.emod_bmod (x := (rs1_val.toNat : Int)) (n := (4294967296))]
  case isFalse hf =>
      congr
      simp only [Nat.sub_zero, Nat.reduceAdd, BitVec.extractLsb_toNat, Nat.shiftRight_zero,
        Nat.reducePow, Int.natCast_emod, Nat.cast_ofNat, BitVec.umod_eq]
      simp at hf
      apply BitVec.eq_of_toInt_eq
      simp only [BitVec.toInt_ofInt, Nat.reducePow, BitVec.toInt_umod, BitVec.extractLsb_toNat,
        Nat.shiftRight_zero, Nat.sub_zero, Nat.reduceAdd, Int.natCast_emod, Nat.cast_ofNat]
      rfl

def REMW_pure64_signed (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  BitVec.signExtend 64
    (BitVec.extractLsb' 0 32
      (BitVec.ofInt (33)
        (if (BitVec.extractLsb 31 0 rs2_val).toInt = 0 then (BitVec.extractLsb 31 0 rs1_val).toInt
        else (BitVec.extractLsb 31 0 rs1_val).toInt.tmod (BitVec.extractLsb 31 0 rs2_val).toInt)))

def REMW_pure64_signed_bv (rs2_val : (BitVec 64)) (rs1_val : (BitVec 64)) : BitVec 64 :=
  BitVec.signExtend 64
      ((BitVec.extractLsb 31 0 rs1_val).srem (BitVec.extractLsb 31 0 rs2_val))

theorem REMW_pure64_signed_eq_REMW_pure64_signed  (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
   REMW_pure64_signed (rs2_val) (rs1_val) = REMW_pure64_signed_bv (rs2_val) (rs1_val) :=
    by
    unfold REMW_pure64_signed REMW_pure64_signed_bv
    rw [extractLsb'_ofInt_eq_ofInt (h:= by simp )]
    congr
    split
    case e_x.isTrue ht  =>
      obtain h': (BitVec.extractLsb 31 0 rs2_val) = 0#_ :=
        BitVec.eq_of_toInt_eq ht
      simp only [Nat.sub_zero, Nat.reduceAdd] at h'
      simp only [h']
      rw [BitVec.ofInt_toInt]
      simp only [Nat.sub_zero, Nat.reduceAdd, BitVec.srem_zero]
    case e_x.isFalse hf =>
      rw [← BitVec.toInt_srem]
      rw [BitVec.ofInt_toInt]

def REM_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64  :=
  BitVec.extractLsb' 0 64
    (BitVec.ofInt (65) (if (rs2_val.toNat: Int) = 0 then (rs1_val.toNat: Int)  else ((rs1_val.toNat : Int )).tmod (rs2_val.toNat : Int)))

def REM_pure64_unsigned_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64  :=
   (if (rs2_val) = 0 then (rs1_val)  else ((rs1_val).umod (rs2_val)))

/- proof in process. The following lemma does not yet exist in Lean's bit vector library.
We are confident that this holds and the lemma is in process of being proven and
added to the bit vector library.
-/
theorem toInt_smod {x y : BitVec w} :
    (x.smod y).toInt = x.toInt.fmod y.toInt := by sorry

theorem  REM_pure64_unsigned_eq_REM_pure64_unsigned_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    REM_pure64_unsigned (rs2_val) (rs1_val) = REM_pure64_unsigned_bv (rs2_val) (rs1_val) := by
  unfold REM_pure64_unsigned REM_pure64_unsigned_bv
  rw [extractLsb'_ofInt_eq_ofInt (h:= by simp )]
  split
  case isTrue isZero =>
      simp only [Int.natCast_eq_zero] at isZero
      obtain rfl : rs2_val = 0#_ :=
        BitVec.eq_of_toNat_eq isZero
      simp
  case isFalse nonZero =>
      simp only [Int.natCast_eq_zero] at nonZero
      simp only [BitVec.ofNat_eq_ofNat, BitVec.umod_eq]
      have h:= (BitVec.toNat_ne_iff_ne (x:=rs2_val) (y:= 0)).mp nonZero
      have h2:= (BitVec.toNat_ne_iff_ne (x:=rs2_val) (y:= 0)).mpr h
      split
      case isTrue => contradiction
      case isFalse =>
        apply BitVec.eq_of_toInt_eq
        simp only [BitVec.toInt_ofInt, Nat.reducePow, BitVec.toInt_umod]
        rfl

def REM_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64  :=
    BitVec.extractLsb' 0 64
    (BitVec.ofInt (65) (if rs2_val.toInt = 0 then rs1_val.toInt else rs1_val.toInt.tmod rs2_val.toInt))

def REM_pure64_signed_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
   rs1_val.srem rs2_val

theorem REM_pure64_signed_eq_REM_pure64_signed_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
    REM_pure64_signed (rs2_val) (rs1_val) = REM_pure64_signed_bv (rs2_val) (rs1_val) := by
  unfold REM_pure64_signed REM_pure64_signed_bv
  rw [extractLsb'_ofInt_eq_ofInt (h:= by simp)]
  split
  case isTrue ht  =>
    simp only [BitVec.ofInt_toInt, BitVec.srem, BitVec.umod_eq, BitVec.neg_eq]
    obtain rfl : rs2_val = 0#_ :=
      BitVec.eq_of_toInt_eq ht
    split <;> simp
  case isFalse hf =>
    rw [← BitVec.toInt_srem ]
    rw [BitVec.ofInt_toInt]

def MULW_pure64 (rs2_val : BitVec 64) (rs1_val :BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64
    (BitVec.extractLsb 31 0
      (BitVec.extractLsb' 0 64
        (BitVec.ofInt 65 ((BitVec.extractLsb 31 0 rs1_val).toInt * (BitVec.extractLsb 31 0 rs2_val).toInt))))

def MULW_pure64_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64
    (((BitVec.extractLsb 31 0 rs1_val) * (BitVec.extractLsb 31 0 rs2_val)))

theorem MULW_pure64_eq_MULW_pure64_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64)  :
  MULW_pure64 (rs2_val) (rs1_val) = MULW_pure64_bv  (rs2_val) (rs1_val) :=
    by
    unfold MULW_pure64 MULW_pure64_bv
    rw [extractLsb'_ofInt_eq_ofInt (h:= by simp)]
    rw [BitVec.extractLsb]
    simp only [Nat.sub_zero, Nat.reduceAdd]
    rw [extractLsb'_ofInt_eq_ofInt (h:= by simp)]
    congr
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_extractLsb, Nat.shiftRight_zero, Nat.sub_zero, Nat.reduceAdd,
      Nat.reducePow, BitVec.toInt_ofInt, Int.mul_bmod_bmod, Int.bmod_mul_bmod, BitVec.toInt_mul]

def MUL_pure64_fff (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
     BitVec.extractLsb 63 0 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toNat * rs2_val.toNat)))

def MUL_pure64_fff_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=  rs2_val * rs1_val

theorem MUL_pure64_fff_eq_MUL_pure64_fff_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :  MUL_pure64_fff  (rs2_val) (rs1_val)
    = MUL_pure64_fff_bv  (rs2_val) (rs1_val ) := by
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
    simp only [Nat.reducePow, Nat.reduceMul] at this
    omega

def  MUL_pure64_fft (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 63 0
    (BitVec.extractLsb' 0 128
      (BitVec.ofInt 129 (Int.ofNat (Int.mul (Int.ofNat rs1_val.toNat)  (rs2_val.toInt)).toNat)))

-- no risc-v instruction maps to this multiplication with the combination of flags ftf.
def MUL_pure64_ftf (rs2_val : BitVec 64) (rs1_val : BitVec 64)  : BitVec 64 :=
  BitVec.extractLsb 63 0 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toInt * rs2_val.toNat)))

def MUL_pure64_ftf_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
   BitVec.extractLsb 63 0 ( (rs1_val * rs2_val))

def MUL_pure64_tff (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toNat * rs2_val.toNat)))

def MUL_pure64_tff_bv  (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
   BitVec.extractLsb 127 64 (BitVec.extractLsb' 0 128 ((BitVec.zeroExtend 128 rs1_val)  * (BitVec.zeroExtend 128 rs2_val)))

theorem MUL_pure64_tff_eq_MUL_pure64_tff_bv  (rs2_val : BitVec 64) (rs1_val : BitVec 64)  :
  MUL_pure64_tff (rs2_val) (rs1_val) = MUL_pure64_tff_bv (rs2_val) (rs1_val) := by
    unfold  MUL_pure64_tff MUL_pure64_tff_bv
    suffices (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (↑rs1_val.toNat * ↑rs2_val.toNat))) =
                 (BitVec.extractLsb' 0 128 (BitVec.zeroExtend 128 rs1_val * BitVec.zeroExtend 128 rs2_val))
      by
      congr
    apply BitVec.eq_of_toNat_eq
    simp only [HMul.hMul, Mul.mul]
    simp only [Int.mul_def, extractLsb'_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofInt,
      Nat.reducePow, Nat.cast_ofNat, BitVec.truncate_eq_setWidth, BitVec.mul_eq,
      BitVec.extractLsb'_eq_self, BitVec.toNat_mul, Nat.mul_mod_mod, Nat.mod_mul_mod]
    congr
    norm_cast
    rw [Int.toNat_natCast]
    have aa := BitVec.isLt rs1_val
    have bb := BitVec.isLt rs2_val
    have cc : 680564733841876926926749214863536422912 = 2^129 := by native_decide
    have aaa : rs1_val.toNat >= 0 := by simp
    have bbb : rs2_val.toNat >= 0 := by simp
    rw [Nat.mod_eq_of_lt (h:=
      by
      rw [cc]
      have := Nat.mul_lt_mul'' (a := rs1_val.toNat) (b := rs2_val.toNat) (c := 2 ^ 64) (d := 2 ^ 64) aa bb
      omega )]
    have := @Nat.mul_lt_mul'' _ _ _ _ aa bb
    simp only [Nat.reducePow, Nat.reduceMul] at this
    omega

theorem extractLsb_setWidth_of_lt (x : BitVec w) (hi lo v : Nat) (hilo : lo < hi) (hhi : hi < v):
    BitVec.extractLsb hi lo (BitVec.setWidth v x) = BitVec.extractLsb hi lo x := by
  simp only [BitVec.extractLsb]
  ext k
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_setWidth, Bool.and_eq_right_iff_imp,
    decide_eq_true_eq]
  omega

def MUL_pure64_ttf (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toInt * rs2_val.toNat)))

def MUL_pure64_ttf_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 (((BitVec.signExtend 129 rs1_val ) * (BitVec.zeroExtend 129 rs2_val )))

theorem MUL_pure64_ttf_eq_MUL_pure64_ttf_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
   MUL_pure64_ttf (rs2_val) (rs1_val) = MUL_pure64_ttf_bv (rs2_val) (rs1_val) := by
  unfold MUL_pure64_ttf MUL_pure64_ttf_bv
  simp
  have h1 : rs1_val.toInt = (rs1_val.signExtend 129).toInt := by
      simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  simp only [h1]
  have h2 : rs2_val.toNat = (rs2_val.zeroExtend 129).toInt := by
      simp only [BitVec.truncate_eq_setWidth, BitVec.toInt_setWidth]
      have : rs2_val.toNat < 2 ^64 := by omega
      have := Nat.pow_lt_pow_of_lt (a := 2) (n := 64) (m := 129) (by omega) (by omega)
      rw [Int.bmod_eq_of_le (n := (rs2_val.toNat : Int)) (by omega) (by omega)]
  rw [h2]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toInt_setWidth, Nat.reducePow, BitVec.ofInt_mul,
    BitVec.ofInt_toInt]
  rw [Int.bmod_eq_of_le (n := (rs2_val.toNat : Int)) (by omega) (by omega)]
  simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  rw [extractLsb_setWidth_of_lt (hi := 127) (lo := 64) (v := 128) (x := BitVec.signExtend 129 rs1_val * BitVec.setWidth 129 rs2_val) (by omega) (by omega)]

def MUL_pure64_ftt (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 63 0 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toInt * rs2_val.toInt)))

def MUL_pure64_ftt_bv  (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
   rs1_val * rs2_val

theorem MUL_pure64_ftt_eq_MUL_pure64_ftt_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :  MUL_pure64_ftt  (rs2_val) (rs1_val )
     = MUL_pure64_ftt_bv  (rs2_val) (rs1_val ) :=
  by
  unfold  MUL_pure64_ftt  MUL_pure64_ftt_bv
  rw [BitVec.extractLsb]
  simp only [Nat.sub_zero, Nat.reduceAdd, extractLsb'_eq_setWidth, Nat.reduceLeDiff,
    BitVec.setWidth_setWidth_of_le]
  have : rs1_val.toInt = (rs1_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  simp only [this]
  have : rs2_val.toInt = (rs2_val.signExtend 129).toInt := by
    simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
  simp only [this]
  rw [BitVec.ofInt_mul]
  simp only [BitVec.ofInt_toInt]
  rw [BitVec.setWidth_mul _ _ (by omega)]
  rw [BitVec.setWidth_signExtend_eq_self (by simp),BitVec.setWidth_signExtend_eq_self (by simp)]

def MUL_pure64_ttt (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toInt * rs2_val.toInt)))

def MUL_pure64_ttt_bv  (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
 BitVec.extractLsb 127 64 ((BitVec.signExtend 129 rs1_val) *  (BitVec.signExtend 129 rs2_val))

theorem MUL_pure64_ttt_eq_MUL_pure64_ttt_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
   MUL_pure64_ttt rs2_val rs1_val  = MUL_pure64_ttt_bv rs2_val rs1_val :=
   by
    unfold MUL_pure64_ttt_bv MUL_pure64_ttt
    have : rs1_val.toInt = (rs1_val.signExtend 129).toInt := by
      simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
    simp only [this]
    have : rs2_val.toInt = (rs2_val.signExtend 129).toInt := by
      simp only [Nat.reduceLeDiff, BitVec.toInt_signExtend_of_le]
    simp only [this]
    rw [BitVec.ofInt_mul]
    simp only [BitVec.ofInt_toInt, extractLsb'_eq_setWidth]
    rw [extractLsb_setWidth_of_lt (hi := 127) (lo := 64) (v := 128) (x := BitVec.signExtend 129 rs1_val * BitVec.signExtend 129 rs2_val) (by omega)]
    simp

-- to do
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
-- to do
def  DIVW_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
       BitVec.signExtend 64
    (BitVec.extractLsb' 0 32
      (BitVec.ofInt 33
        (if (rs2_val.toNat: Int)  % 4294967296 = 0 then -1
        else ((rs1_val.toNat : Int) % 4294967296).tdiv ((rs2_val.toNat : Int) % 4294967296))))

def DIV_pure64_signed (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb' 0 64
    (BitVec.ofInt 65
      (if ((2^63)-1) < if rs2_val.toInt = 0 then -1 else rs1_val.toInt.tdiv rs2_val.toInt then
         -(2^63)
      else if rs2_val.toInt = 0 then -1 else rs1_val.toInt.tdiv rs2_val.toInt))

def DIV_pure64_signed_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  if rs2_val = 0#64 then
    -1#64
  else
    rs1_val.sdiv rs2_val

theorem DIV_pure64_signed_eq_DIV_pure64_signed_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64)  :
  DIV_pure64_signed (rs2_val) (rs1_val ) = DIV_pure64_signed_bv (rs2_val) (rs1_val ) := by
    unfold DIV_pure64_signed DIV_pure64_signed_bv
    rw [extractLsb'_ofInt_eq_ofInt (h:= by simp)]
    by_cases h1 : rs2_val = 0#64
    case pos => simp [h1]
    case neg =>
      have h' : rs2_val.toInt ≠ 0 := by
        have h1 := (BitVec.toInt_ne).mpr h1
        exact h1
      apply BitVec.eq_of_toInt_eq
      simp only [Int.reduceSub, h', ↓reduceIte, Int.reduceNeg, BitVec.toInt_ofInt, h1]
      simp only [Int.reducePow, Int.reduceSub, Int.reduceNeg, Nat.reducePow, BitVec.toInt_sdiv]
      by_cases h : rs1_val = .intMin _ ∧ rs2_val = -1#64
      case pos =>
          obtain ⟨rfl, rfl⟩ := h
          simp only [BitVec.toInt_intMin, Nat.add_one_sub_one, Nat.reducePow, Nat.reduceMod,
            Nat.cast_ofNat, Int.reduceNeg, BitVec.reduceNeg, BitVec.reduceToInt, Int.tdiv_neg,
            Int.tdiv_one, neg_neg, Int.reduceLT, ↓reduceIte, Int.reduceBmod]
      case neg =>
          have := BitVec.toInt_sdiv_of_ne_or_ne rs1_val rs2_val <| by
              rw [← Decidable.not_and_iff_not_or_not]
              exact h
          rw[← this]
          split
          case isTrue iT =>
            have intMax : (BitVec.intMax 64).toInt =  9223372036854775807 := by native_decide
            have h3 : (rs1_val.sdiv rs2_val).toInt ≤2 ^ 63  - 1 := by
                apply  BitVec.toInt_le
            simp only [Int.reducePow, Int.reduceSub] at h3
            exact (not_le_of_lt iT h3).elim
          case isFalse iF =>
          rfl

def DIV_pure64_unsigned (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb' 0 64 (BitVec.ofInt 65 (if ((rs2_val.toNat):Int) = 0 then -1 else (rs1_val.toNat : Int).tdiv (rs2_val.toNat: Int)))

def DIV_pure64_unsigned_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  if rs2_val = 0#64 then  (-1)  else rs1_val.udiv rs2_val

theorem  DIV_pure64_unsigned_eq_DIV_pure64_unsigned_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
      DIV_pure64_unsigned (rs2_val ) (rs1_val)  = DIV_pure64_unsigned_bv (rs2_val ) (rs1_val) := by
  unfold DIV_pure64_unsigned DIV_pure64_unsigned_bv
  split
  case isTrue ht =>
      simp only [Int.reduceNeg, BitVec.reduceOfInt, extractLsb'_eq_setWidth, Nat.reduceLeDiff,
        BitVec.setWidth_ofNat_of_le, BitVec.reduceOfNat, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg,
        BitVec.udiv_eq]
      simp only [Int.natCast_eq_zero] at ht
      have h3 :=  BitVec.eq_of_toNat_eq (x :=  rs2_val) (y:= 0) ht
      simp only [h3, BitVec.ofNat_eq_ofNat, ↓reduceIte]
  case isFalse hf =>
      simp only [extractLsb'_eq_setWidth, BitVec.ofNat_eq_ofNat, BitVec.reduceNeg]
      split
      case isTrue htt =>
          simp at hf
          bv_omega
      · rw [BitVec.setWidth_eq_extractLsb' (by simp)]
        rw [extractLsb'_ofInt_eq_ofInt (h:= by simp)]
        apply BitVec.eq_of_toInt_eq
        simp only [BitVec.toInt_ofInt]
        have aa := BitVec.isLt (rs1_val.udiv rs2_val)
        rw [BitVec.udiv.eq_1 ]
        rw[← Int.ofNat_tdiv]
        rw [BitVec.toInt_eq_toNat_bmod]
        simp only [Int.natCast_ediv, Nat.reducePow, BitVec.toNat_ofNatLT]

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

def  ITYPE_pure64_RISCV_XORI (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
      let immext : BitVec 64 := (BitVec.signExtend 64 imm) ;
      BitVec.xor rs1_val immext

def ZICOND_RTYPE_pure64_RISCV_CZERO_EQZ (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
      (if rs2_val = BitVec.zero 64 then BitVec.zero 64 else rs1_val)

def ZICOND_RTYPE_pure64_RISCV_RISCV_CZERO_NEZ (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
   (if rs2_val = BitVec.zero 64 then rs1_val else BitVec.zero 64)

def ZBS_RTYPE_pure64_RISCV_BCLR (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.and rs1_val (BitVec.not (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) (BitVec.extractLsb  5 0 rs2_val).toNat))

def ZBS_RTYPE_pure64_RISCV_BCLR_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.and rs1_val (BitVec.not ((BitVec.zeroExtend 64 1#1) <<< (BitVec.extractLsb  5 0 rs2_val)))

theorem ZBS_RTYPE_pure64_RISCV_BCLR_eq_ZBS_RTYPE_pure64_RISCV_BCLR_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  ZBS_RTYPE_pure64_RISCV_BCLR (rs2_val) (rs1_val) =  ZBS_RTYPE_pure64_RISCV_BCLR_bv (rs2_val) (rs1_val) :=
    by
    unfold ZBS_RTYPE_pure64_RISCV_BCLR ZBS_RTYPE_pure64_RISCV_BCLR_bv
    bv_normalize

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

def ZBS_RTYPE_pure64_RISCV_BEXT_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64)  :=
  BitVec.setWidth 64
    (match
      BitVec.and rs1_val ( (BitVec.setWidth 64 1#1) <<< (BitVec.extractLsb 5 0 rs2_val)) !=
        0#64 with
    | true => 1#1
    | false => 0#1)

theorem ZBS_RTYPE_pure64_RISCV_BEXT_eq_ZBS_RTYPE_pure64_RISCV_BEXT_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  ZBS_RTYPE_pure64_RISCV_BEXT (rs2_val) (rs1_val) = ZBS_RTYPE_pure64_RISCV_BEXT_bv (rs2_val) (rs1_val) :=
    by
    unfold ZBS_RTYPE_pure64_RISCV_BEXT  ZBS_RTYPE_pure64_RISCV_BEXT_bv
    simp

 def ZBS_RTYPE_pure64_BINV (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.xor rs1_val  (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) (BitVec.extractLsb 5 0 rs2_val).toNat)

 def ZBS_RTYPE_pure64_BINV_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.xor rs1_val  ((BitVec.zeroExtend 64 1#1) <<< (BitVec.extractLsb 5 0 rs2_val))

theorem ZBS_RTYPE_pure64_BINV_eq_ZBS_RTYPE_pure64_BINV_bv  (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  ZBS_RTYPE_pure64_BINV (rs2_val) (rs1_val)  = ZBS_RTYPE_pure64_BINV_bv rs2_val rs1_val :=
  by
  unfold ZBS_RTYPE_pure64_BINV ZBS_RTYPE_pure64_BINV_bv
  bv_decide

def ZBS_RTYPE_pure64_RISCV_BSET (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.or rs1_val (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) (BitVec.extractLsb 5 0 rs2_val).toNat)

def ZBS_RTYPE_pure64_RISCV_BSET_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.or rs1_val ((BitVec.zeroExtend 64 1#1) <<< (BitVec.extractLsb 5 0 rs2_val))

theorem ZBS_RTYPE_pure64_RISCV_BSET_eq_ZBS_RTYPE_pure64_RISCV_BSET_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  ZBS_RTYPE_pure64_RISCV_BSET (rs2_val) (rs1_val) = ZBS_RTYPE_pure64_RISCV_BSET_bv (rs2_val) (rs1_val) :=
   by
   unfold ZBS_RTYPE_pure64_RISCV_BSET ZBS_RTYPE_pure64_RISCV_BSET_bv
   simp

def ZBS_IOP_pure64_RISCV_BCLRI (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.and rs1_val (BitVec.not (BitVec.shiftLeft (BitVec.setWidth 64 1#1) (shamt.toNat)))

def ZBS_IOP_pure64_RISCV_BCLRI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.and rs1_val (BitVec.not ( (BitVec.setWidth 64 1#1) <<< shamt))

theorem ZBS_IOP_pure64_RISCV_BCLRI_eq_ZBS_IOP_pure64_RISCV_BCLRI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) :
   ZBS_IOP_pure64_RISCV_BCLRI (shamt) (rs1_val ) = ZBS_IOP_pure64_RISCV_BCLRI_bv (shamt) (rs1_val) :=
    by
    unfold  ZBS_IOP_pure64_RISCV_BCLRI ZBS_IOP_pure64_RISCV_BCLRI_bv
    simp

def ZBS_IOP_pure64_RISCV_BEXTI (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.setWidth 64
      (match (BitVec.and (rs1_val) (BitVec.shiftLeft (BitVec.setWidth 64 1#1) shamt.toNat)) != 0#64 with
      | true => 1#1
      | false => 0#1)

def ZBS_IOP_pure64_RISCV_BEXTI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.setWidth 64
      (match (BitVec.and (rs1_val) ( (BitVec.setWidth 64 1#1) <<< shamt)) != 0#64 with
      | true => 1#1
      | false => 0#1)

theorem  ZBS_IOP_pure64_RISCV_BEXTI_eq_ZBS_IOP_pure64_RISCV_BEXTI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) :
  ZBS_IOP_pure64_RISCV_BEXTI (shamt) (rs1_val ) = ZBS_IOP_pure64_RISCV_BEXTI_bv (shamt ) (rs1_val ) :=
  by
  unfold ZBS_IOP_pure64_RISCV_BEXTI  ZBS_IOP_pure64_RISCV_BEXTI_bv
  simp

def ZBS_IOP_pure64_RISCV_BINVI (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.xor rs1_val  (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) shamt.toNat)

def ZBS_IOP_pure64_RISCV_BINVI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.xor rs1_val  ( (BitVec.zeroExtend 64 1#1) <<< shamt)

theorem ZBS_IOP_pure64_RISCV_BINVI_eq_ZBS_IOP_pure64_RISCV_BINVI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) :
  ZBS_IOP_pure64_RISCV_BINVI (shamt) (rs1_val) = ZBS_IOP_pure64_RISCV_BINVI_bv (shamt ) (rs1_val) :=
   by
   unfold ZBS_IOP_pure64_RISCV_BINVI ZBS_IOP_pure64_RISCV_BINVI_bv
   rfl

def ZBS_IOP_pure64_RISCV_BSETI (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.or rs1_val (BitVec.shiftLeft (BitVec.zeroExtend 64 1#1) shamt.toNat)

def ZBS_IOP_pure64_RISCV_BSETI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) :=
  BitVec.or rs1_val ((BitVec.zeroExtend 64 1#1) <<< shamt)

theorem ZBS_IOP_pure64_RISCV_BSETI_eq_ZBS_IOP_pure64_RISCV_BSETI_bv (shamt : BitVec 6) (rs1_val : BitVec 64) :
  ZBS_IOP_pure64_RISCV_BSETI (shamt) (rs1_val) =   ZBS_IOP_pure64_RISCV_BSETI_bv (shamt) (rs1_val) :=
    by
    unfold ZBS_IOP_pure64_RISCV_BSETI  ZBS_IOP_pure64_RISCV_BSETI_bv
    simp

-- won't ever transform this
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

 def ZBB_RTYPE_pure64_RISCV_ROL_bv  (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
  BitVec.or (BitVec.shiftLeft  rs1_val (BitVec.extractLsb 5 0 rs2_val).toNat)
    (rs1_val >>> (BitVec.extractLsb' 0 6 (64#7) - BitVec.extractLsb 5 0 rs2_val))

theorem ZBB_RTYPE_pure64_RISCV_ROL_eq_ZBB_RTYPE_pure64_RISCV_ROL_bv  (rs2_val : BitVec 64) (rs1_val : BitVec 64)  :
  ZBB_RTYPE_pure64_RISCV_ROL  (rs2_val ) (rs1_val ) =  ZBB_RTYPE_pure64_RISCV_ROL_bv  (rs2_val) (rs1_val) :=
    by
    unfold ZBB_RTYPE_pure64_RISCV_ROL ZBB_RTYPE_pure64_RISCV_ROL_bv
    simp

 def ZBB_RTYPE_pure64_RISCV_ROR (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
      BitVec.or (BitVec.ushiftRight rs1_val (BitVec.extractLsb 5 0 rs2_val).toNat)
    (BitVec.shiftLeft rs1_val ((BitVec.extractLsb' 0 6 (BitVec.ofInt (7) (64)) - BitVec.extractLsb 5 0 rs2_val)).toNat)

 def ZBB_RTYPE_pure64_RISCV_ROR_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
      BitVec.or ( rs1_val >>> (BitVec.extractLsb 5 0 rs2_val))
    ( rs1_val  <<<  ((BitVec.extractLsb' 0 6 (BitVec.ofInt (7) (64)) - BitVec.extractLsb 5 0 rs2_val)))

theorem ZBB_RTYPE_pure64_RISCV_ROR_eq_ZBB_RTYPE_pure64_RISCV_ROR_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) :
  ZBB_RTYPE_pure64_RISCV_ROR (rs2_val) (rs1_val) = ZBB_RTYPE_pure64_RISCV_ROR_bv (rs2_val) (rs1_val) :=
    by
    unfold ZBB_RTYPE_pure64_RISCV_ROR  ZBB_RTYPE_pure64_RISCV_ROR_bv
    simp

 def ZBA_RTYPEUW_pure64_RISCV_ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
      BitVec.zeroExtend 64 (BitVec.extractLsb 31 0 rs1_val) <<< 0#2 + rs2_val

def  ZBA_RTYPEUW_pure64_RISCV_SH1ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
    BitVec.add (BitVec.zeroExtend (64) (BitVec.extractLsb 31 0 rs1_val) <<< 1#2)  (rs2_val)

def ZBA_RTYPEUW_pure64_RISCV_SH2ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
      BitVec.add (BitVec.zeroExtend (64) (BitVec.extractLsb 31 0 rs1_val) <<< 2#2) rs2_val

def  ZBA_RTYPEUW_pure64_RISCV_SH3ADDUW (rs2_val : BitVec 64) (rs1_val : BitVec 64) :=
      BitVec.add (BitVec.zeroExtend (64) (BitVec.extractLsb 31 0 rs1_val) <<< 3#2)  rs2_val

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
end pure_semantics
