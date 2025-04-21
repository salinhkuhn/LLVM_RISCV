import RiscvDialect.LLVMRiscv.PeepholeRewriteRefine

open llvm.riscv
open riscv.semantics
open LLVM

-- llvm.add
def add_llvm : Com  llvm.riscv [.opt64, .opt64] .pure .opt64  := [_| {
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

def llvm_add_lower_riscv : RiscVPeepholeRewriteRefine [Ty.opt64, Ty.opt64] :=
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
  Com llvm.riscv (Ctxt.ofList [.opt64, .opt64]) .pure .opt64 := rewritePeepholeAt (RiscVPeepholeRewriteRefine.toPeepholeUNSOUND llvm_add_lower_riscv) 1  add_riscv
-- if dont provide a proof it fails to apply/ display the rewrite.
#eval add_cast_eq_add_elim_rewrite
