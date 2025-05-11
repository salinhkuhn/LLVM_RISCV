import RiscvDialect.LLVMRiscv.InstructionSelection.add_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.and_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.ashr_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.const_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.mul_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.or_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.rem_lowering
--import RiscvDialect.LLVMRiscv.InstructionSelection.remw_lowering -- unsure if that since a llvm instruction might not be lowered to it
import RiscvDialect.LLVMRiscv.InstructionSelection.sdiv_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.shl_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.srl_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.sub_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.udiv_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.urem_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.xor_lowering
import RiscvDialect.LLVMRiscv.InstructionSelection.xor_lowering
import RiscvDialect.LLVMRiscv.Refinement
import RiscvDialect.LLVMRiscv.forLeanMlir

set_option maxRecDepth 10000000 -- we set this to be able to evaluate the lowered expression

/-! # Instruction selection-/
/-- This file will contain the lowering pattersn to pass to the multi_peephole rewriter.
To then actually perform instruction selection, we will have multiple arrays containing the rewritting patterns. -/

--def const_match := sorry -- TO DO

def add_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
    [llvm_add_lower_riscv_noflags,llvm_add_lower_riscv_nsw_flag, llvm_add_lower_riscv_nuw_flag, llvm_add_lower_riscv_nuw_nsw_flag]

def and_match :=  List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND [llvm_and_lower_riscv]

def ashr_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
    [llvm_ashr_lower_riscv_no_flag,llvm_ashr_lower_riscv_flag]

def const_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
    [llvm_const_lower_riscv_li_0] -- here we lower constant only up to a certain value, since the framework does not support matching on values yet.

def mul_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
    [llvm_mul_lower_riscv_noflag, llvm_mul_lower_riscv_flags, llvm_mul_lower_riscv_nsw_flag, llvm_mul_lower_riscv_nuw_flag]

def or_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
    [llvm_or_lower_riscv1_noflag, llvm_or_lower_riscv_disjoint]

def rem_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND [llvm_rem_lower_riscv]

def sdiv_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
     [llvm_sdiv_lower_riscv_no_flag, llvm_sdiv_lower_riscv_exact]

def shl_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
     [llvm_shl_lower_riscv, llvm_shl_lower_riscv_nsw, llvm_shl_lower_riscv_nuw,llvm_shl_lower_riscv_nsw_nuw ]

def srl_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND [llvm_srl_lower_riscv,llvm_srl_lower_riscv_exact]

def sub_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
     [llvm_sub_lower_riscv_no_flag,llvm_sub_nuw_lower_riscv, llvm_sub_nsw_lower_riscv, llvm_sub_nuw_lower_riscv]

def udiv_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
    [llvm_udiv_lower_riscv_no_flag, llvm_udiv_lower_riscv_flag]

def urem_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND [llvm_urem_lower_riscv ]
def xor_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND [llvm_xor_lower_riscv]

--- to do : double check, especially if all constants are covered.
def loweringPass :=
  List.flatten [
    add_match,
    and_match,
    ashr_match,
    mul_match,
    or_match,
    rem_match,
    sdiv_match,
    shl_match,
    srl_match,
    sub_match,
    udiv_match,
    urem_match,
    xor_match
  ]
-- TO DO: rethink this pass
def reconcile_cast_pass_llvm := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND [double_cast_elimination_LLVM_to_RISCV, cast_eliminiation_llvm] -- I want to modell this as a separat pass after performing the lowerings.


/- ! example workflow
mlir opt tool -> input the llvm ir program -> parse it as a com -> call my function for the lowering -> riscv coms with conversion casts -/
open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM)

def test01 := [LV|
{
^0(%0: i64):
  --%0 = llvm.mlir.constant (10) : i64
 %3 = llvm.and %0, %0 : i64
  llvm.return %3 : i64
} ]

#check rewritePeephole_multi
def lower :
   Com LLVMPlusRiscV (Ctxt.ofList [.llvm (.bitvec 64)]) .pure (.llvm (.bitvec 64)) :=
  rewritePeephole_multi LLVMPlusRiscV (100) loweringPass test01
#eval! lower
