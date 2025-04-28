import RiscvDialect.LLVMRiscv.PeepholeRewriteRefine

open llvm.riscv
open riscv.semantics
open LLVM

-- llvm.add
def add_llvm : Com  llvm.riscv [.bitvec, .bitvec] .pure .bitvec  := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %add = "llvm.add"(%lhs, %rhs) : (!i64, !i64) -> !i64
      "return" (%add) : (!i64) -> ()
  }]
#eval add_llvm

-- riscv.add
def add_riscv := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %lhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%lhs) : (!i64) -> !r64
      %rhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%rhs) : (!i64) -> !r64
      %add = "riscv.add"(%lhsr, %rhsr) : (!r64, !r64) -> !r64
      %addl = "builtin.unrealized_conversion_cast.riscvToLLVM" (%add) : (!r64) -> (!i64)
      "return" (%addl) : (!i64) -> ()
  }]

def llvm_add_lower_riscv : RiscVPeepholeRewriteRefine [Ty.bitvec, Ty.bitvec] :=
  {lhs:= add_llvm , rhs:= add_riscv ,
   correct := by
    unfold add_llvm add_riscv
    simp_peephole
    simp [riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM,
      riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv,
      riscv.semantics.RTYPE_pure64_RISCV_ADD,
      add, liftM, monadLift, MonadLift.monadLift,
      BitVec.Refinement.some_some
      ]
    rintro (_|_) (_|_) <;> simp [add?]
  }


/- # AND -/
def and_llvm : Com  llvm.riscv [.bitvec, .bitvec] .pure .bitvec  := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %add = "llvm.and"(%lhs, %rhs) : (!i64, !i64) -> !i64
      "return" (%add) : (!i64) -> ()
  }]
def and_riscv := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %lhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%lhs) : (!i64) -> !r64
      %rhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%rhs) : (!i64) -> !r64
      %add = "riscv.and"(%lhsr, %rhsr) : (!r64, !r64) -> !r64
      %addl = "builtin.unrealized_conversion_cast.riscvToLLVM" (%add) : (!r64) -> (!i64)
      "return" (%addl) : (!i64) -> ()
  }]

def llvm_and_lower_riscv : RiscVPeepholeRewriteRefine [Ty.bitvec, Ty.bitvec] :=
  {lhs:= and_llvm , rhs:= and_riscv ,
   correct := by
    unfold and_llvm and_riscv
    simp_peephole
    simp [riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM,  riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_SUB]
    simp [LLVM.and, RTYPE_pure64_RISCV_AND]
    rintro (_|_) (_|_) <;> simp [and?]; bv_decide
  }


/- # ASHR  -/

def ashr_llvm : Com  llvm.riscv [.bitvec, .bitvec] .pure .bitvec  := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %add = "llvm.ashr"(%lhs, %rhs) : (!i64, !i64) -> !i64
      "return" (%add) : (!i64) -> ()
  }]
#eval ashr_llvm
-- riscv.add
def sra_riscv := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %lhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%lhs) : (!i64) -> !r64
      %rhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%rhs) : (!i64) -> !r64
      %add = "riscv.sra"(%lhsr, %rhsr) : (!r64, !r64) -> !r64
      %addl = "builtin.unrealized_conversion_cast.riscvToLLVM" (%add) : (!r64) -> (!i64)
      "return" (%addl) : (!i64) -> ()
  }]

def llvm_ahr_lower_riscv : RiscVPeepholeRewriteRefine [Ty.bitvec, Ty.bitvec] :=
  {lhs:= ashr_llvm , rhs:= sra_riscv ,
   correct := by
    unfold ashr_llvm sra_riscv
    simp_peephole
    simp [riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM,  riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_SRA]
   --help
    --rintro (_|_) (_|_) <;> simp [];
  }
/- # LSHR  -/



/- # MUL  -/
def mul_llvm : Com  llvm.riscv [.bitvec, .bitvec] .pure .bitvec  := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %add = "llvm.mul"(%lhs, %rhs) : (!i64, !i64) -> !i64
      "return" (%add) : (!i64) -> ()
  }]
#eval mul_llvm
-- riscv.add
def mul_riscv := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %lhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%lhs) : (!i64) -> !r64
      %rhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%rhs) : (!i64) -> !r64
      %add = "riscv.mul"(%lhsr, %rhsr) : (!r64, !r64) -> !r64
      %addl = "builtin.unrealized_conversion_cast.riscvToLLVM" (%add) : (!r64) -> (!i64)
      "return" (%addl) : (!i64) -> ()
  }]

def llvm_mul_lower_riscv : RiscVPeepholeRewriteRefine [Ty.bitvec, Ty.bitvec] :=
  {lhs:= mul_llvm , rhs:= mul_riscv ,
   correct := by
    unfold mul_llvm mul_riscv
    simp_peephole
    simp [riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM,  riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv, MUL_pure64_ftt]
    rintro (_|_) (_|_) <;> simp [mul]
    . simp [mul?] --HELP
      bv_decide



/-

    simp [riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM,
      riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv,
      riscv.semantics.RTYPE_pure64_RISCV_ADD,
      add, liftM, monadLift, MonadLift.monadLift,
      BitVec.Refinement.some_some
      ]
      -/

  }

/- # NEG , not in llvm  -/


/- # NOT , not in llvm   -/


/- # OR   -/
def or_llvm : Com  llvm.riscv [.bitvec, .bitvec] .pure .bitvec  := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %add = "llvm.or"(%lhs, %rhs) : (!i64, !i64) -> !i64
      "return" (%add) : (!i64) -> ()
  }]
def or_riscv := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %lhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%lhs) : (!i64) -> !r64
      %rhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%rhs) : (!i64) -> !r64
      %add = "riscv.or"(%lhsr, %rhsr) : (!r64, !r64) -> !r64
      %addl = "builtin.unrealized_conversion_cast.riscvToLLVM" (%add) : (!r64) -> (!i64)
      "return" (%addl) : (!i64) -> ()
  }]

def llvm_or_lower_riscv : RiscVPeepholeRewriteRefine [Ty.bitvec, Ty.bitvec] :=
  {lhs:= or_llvm , rhs:= or_riscv ,
   correct := by
    unfold or_llvm or_riscv
    simp_peephole
    simp [riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM,  riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_OR, DisjointFlag.mk]
    rintro (_|_) (_|_) <;> simp

   -- bv_decide
  }

/- # REM  -/


/- # SDIV   -/

/- # SHL   -/
def sll_llvm : Com  llvm.riscv [.bitvec, .bitvec] .pure .bitvec  := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %add = "llvm.shl"(%lhs, %rhs) : (!i64, !i64) -> !i64
      "return" (%add) : (!i64) -> ()
  }]
#eval sll_llvm

-- riscv.add
def sll_riscv := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %lhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%lhs) : (!i64) -> !r64
      %rhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%rhs) : (!i64) -> !r64
      %add = "riscv.sll"(%lhsr, %rhsr) : (!r64, !r64) -> !r64
      %addl = "builtin.unrealized_conversion_cast.riscvToLLVM" (%add) : (!r64) -> (!i64)
      "return" (%addl) : (!i64) -> ()
  }]

axiom X : Prop
axiom Y : Prop
axiom Z : Prop

-- (a b : Nat) ()
-- subtraction_self_inverse
-- sub_add_eq
-- sub_eq_zero
-- sub_self_eq

def llvm_sll_lower_riscv : RiscVPeepholeRewriteRefine [Ty.bitvec, Ty.bitvec] :=
  {lhs:= sll_llvm , rhs:= sll_riscv ,
   correct := by
    unfold sll_llvm sll_riscv
    simp_peephole
    simp only [builtin.unrealized_conversion_cast.riscvToLLVM, RTYPE_pure64_RISCV_SLL,
      builtin.unrealized_conversion_cast.LLVMToriscv, Nat.sub_zero, Nat.reduceAdd,
      BitVec.extractLsb_toNat, Nat.shiftRight_zero, Nat.reducePow, BitVec.shiftLeft_eq]
    simp only [shl, Bool.false_eq_true, BitVec.shiftLeft_eq', BitVec.sshiftRight_eq', ne_eq,
      false_and, ↓reduceIte, BitVec.ushiftRight_eq', Option.bind_eq_bind]

    rintro (_|v) (_|w) <;> simp only [shl?, Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, ge_iff_le,
      BitVec.shiftLeft_eq', Option.some_bind, Option.none_bind, Option.getD_none, Option.getD_some,
      BitVec.zero_shiftLeft, BitVec.Refinement.none_left]
    split
    case isTrue h =>
      simp [BitVec.Refinement]
    case isFalse h =>
      simp only [BitVec.Refinement.some_some]
      have h₁ (n : Nat) (b : Nat) (premise : (b < n) ) :  (b % n) = b := by
        exact Nat.mod_eq_of_lt premise
      have shift_left_mod {n : Nat} (a : BitVec n) (b : Nat)(h : b < n) :
        a <<< b = a <<< (b % n) := by
        rw [h₁]
        exact h
      apply shift_left_mod
      simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, not_le] at h
      exact h
  }


/- # SUB   -/
def sub_llvm : Com  llvm.riscv [.bitvec, .bitvec] .pure .bitvec  := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %add = "llvm.sub"(%lhs, %rhs) : (!i64, !i64) -> !i64
      "return" (%add) : (!i64) -> ()
  }]
#eval sub_llvm

-- riscv.add
def sub_riscv := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %lhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%lhs) : (!i64) -> !r64
      %rhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%rhs) : (!i64) -> !r64
      %add = "riscv.sub"(%lhsr, %rhsr) : (!r64, !r64) -> !r64
      %addl = "builtin.unrealized_conversion_cast.riscvToLLVM" (%add) : (!r64) -> (!i64)
      "return" (%addl) : (!i64) -> ()
  }]

def llvm_sub_lower_riscv : RiscVPeepholeRewriteRefine [Ty.bitvec, Ty.bitvec] :=
  {lhs:= sub_llvm , rhs:= sub_riscv ,
   correct := by
    unfold sub_llvm sub_riscv
    simp_peephole
    simp [riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM,  riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_SUB]
    simp [sub]
    rintro (_|_) (_|_) <;> simp [sub?]
  }


/- # UDIV   -/

/- # UREM   -/

/- # XOR   -/
def xor_llvm : Com  llvm.riscv [.bitvec, .bitvec] .pure .bitvec  := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %add = "llvm.xor"(%lhs, %rhs) : (!i64, !i64) -> !i64
      "return" (%add) : (!i64) -> ()
  }]
#eval sub_llvm

-- riscv.add
def xor_riscv := [_| {
    ^entry (%lhs: !i64, %rhs: !i64 ):
      %lhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%lhs) : (!i64) -> !r64
      %rhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%rhs) : (!i64) -> !r64
      %add = "riscv.xor"(%lhsr, %rhsr) : (!r64, !r64) -> !r64
      %addl = "builtin.unrealized_conversion_cast.riscvToLLVM" (%add) : (!r64) -> (!i64)
      "return" (%addl) : (!i64) -> ()
  }]

def llvm_xor_lower_riscv : RiscVPeepholeRewriteRefine [Ty.bitvec, Ty.bitvec] :=
  {lhs:= xor_llvm , rhs:= xor_riscv ,
   correct := by
    unfold xor_llvm xor_riscv
    simp_peephole
    simp [riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM,  riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_XOR]
    rintro (_|_) (_|_) <;> simp [LLVM.xor]
    simp [xor?]
    bv_decide
  }


/-
[riscv.semantics.builtin.unrealized_conversion_cast.riscvToLLVM,
      riscv.semantics.builtin.unrealized_conversion_cast.LLVMToriscv,
      riscv.semantics.RTYPE_pure64_RISCV_ADD,
      add, liftM, monadLift, MonadLift.monadLift,
      BitVec.Refinement.some_some
      ]


-/




























/--
## Testing the application of cast "folding" pass/rewrites.
-- zero optimization
def ex1_rewritePeepholeAtO0 :
    Com RV64 (Ctxt.ofList [.bv]) .pure .bv := rewritePeepholeAt rewrite_and0 0 lhs_and0

-- optimized code
def ex1_rewritePeepholeAtO1 :
    Com RV64 (Ctxt.ofList [.bv]) .pure .bv := rewritePeepholeAt rewrite_and0 1 lhs_and0
-/


def add_cast_eq_add_elim_rewrite :
  Com llvm.riscv (Ctxt.ofList [.bitvec, .bitvec]) .pure .bitvec := rewritePeepholeAt (RiscVPeepholeRewriteRefine.toPeepholeUNSOUND llvm_add_lower_riscv) 1  add_riscv
-- if dont provide a proof it fails to apply/ display the rewrite.

#eval add_cast_eq_add_elim_rewrite
