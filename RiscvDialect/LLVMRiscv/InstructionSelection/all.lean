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

 -- TO DO const

def add_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
    [llvm_add_lower_riscv_noflags,llvm_add_lower_riscv_nsw_flag, llvm_add_lower_riscv_nuw_flag, llvm_add_lower_riscv_nuw_nsw_flag]

def and_match :=  List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND [llvm_and_lower_riscv]

def ashr_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
    [llvm_ashr_lower_riscv_no_flag,llvm_ashr_lower_riscv_flag]

def const_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
    [ llvm_const_lower_riscv_li_neg1, llvm_const_lower_riscv_li_0, llvm_const_lower_riscv_li_1, llvm_const_lower_riscv_li_2] -- here we lower constant only up to a certain value, since the framework does not support matching on values yet.

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

def sub_match_self :=  List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND  [llvm_sub_lower_riscv_no_flag_self]

def sub_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
     [ llvm_sub_lower_riscv_no_flag,llvm_sub_nuw_lower_riscv, llvm_sub_nsw_lower_riscv, llvm_sub_nuw_lower_riscv]
def udiv_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND
    [llvm_udiv_lower_riscv_no_flag, llvm_udiv_lower_riscv_flag]

def urem_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND [llvm_urem_lower_riscv ]
def xor_match := List.map LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND [llvm_xor_lower_riscv]

--- to do : double check, especially if all constants are covered.
def loweringPassConst := List.flatten [const_match]  -- no input there can't b^put into the other array because then would complain.
def loweringPassSingle := List.flatten [ sub_match_self]

-- ask question about making this list here generic over the length of the context.
def loweringPass:=
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
-- ask how to make this type generic !

/- def loweringPass {σs : List LLVMRiscV.Ty } :   List (PeepholeRewrite LLVMRiscV.LLVMPlusRiscV σs (LLVMRiscV.Ty.llvm (InstCombine.Ty.bitvec 64))) :=
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
  ] -/





-- how to write this in a more generic way.
--[LLVMRiscV.Ty.llvm (InstCombine.Ty.bitvec 64), LLVMRiscV.Ty.llvm (InstCombine.Ty.bitvec 64)]




/-
 List
    (PeepholeRewrite LLVMRiscV.LLVMPlusRiscV
      [LLVMRiscV.Ty.llvm (InstCombine.Ty.bitvec 64), LLVMRiscV.Ty.llvm (InstCombine.Ty.bitvec 64)]
      (LLVMRiscV.Ty.llvm (InstCombine.Ty.bitvec 64)))

-/
-- TO DO: rethink this pass
def reconcile_cast_pass_llvm := List.map RiscVToLLVMPeepholeRewriteRefine.toPeepholeUNSOUND [cast_eliminiation_riscv] -- [double_cast_elimination_LLVM_to_RISCV, cast_eliminiation_llvm] -- I want to modell this as a separat pass after performing the lowerings.
