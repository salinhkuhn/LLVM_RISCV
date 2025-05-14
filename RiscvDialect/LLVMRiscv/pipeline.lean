import RiscvDialect.LLVMRiscv.LLVMAndRiscV
import SSA.Projects.DCE.DCE
import SSA.Projects.CSE.CSE
import RiscvDialect.LLVMRiscv.forLeanMlir
import RiscvDialect.LLVMRiscv.InstructionSelection.all

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM)

set_option maxRecDepth 10000000

/- fuel_def defines the fuel for the recurson and is the maximum steps taken.
I tried to define it using the size of the program to be lowered. -/
def nr_of_rewrites := 10
def fuel_def {d : Dialect} [DialectSignature d] {Γ : Ctxt d.Ty} {eff : EffectKind} {t : d.Ty} (p: Com d Γ eff t) : Nat := max (Com.size p) nr_of_rewrites


-- to do: this example stack overflows when performing the lowering.
def llvm00:=
      [LV|{
      ^bb0(%X : i64, %Y : i64 ):
      %1 = llvm.add %X, %Y : i64
      %2 = llvm.sub %X, %X : i64 -- this instruction atm is encoded as a separate pattern.
      %3 = llvm.add %2, %Y : i64
      %4 = llvm.add %3, %Y : i64
      %5 = llvm.add %3, %4 : i64
      llvm.return %5 : i64
  }]
/-
experiment 01:
obsereved best scheduling of the passes, pass ordering problem,
here I first rewriter the binarop operations using the same operand twice.
Then eliminate deadcode. Then apply the lowering pass and then the cast_elimination pass.  -/
def test_peep0_single :  Com LLVMPlusRiscV (Ctxt.ofList [.llvm (.bitvec 64),.llvm (.bitvec 64)]) .pure (.llvm (.bitvec 64)) :=
  rewritePeephole_multi LLVMPlusRiscV (fuel_def llvm00) (loweringPassSingle) llvm00
#eval! test_peep0_single
def test_pep0_dce:= (DCE.dce' test_peep0_single)
#eval! test_pep0_dce
def test_peep0 :  Com LLVMPlusRiscV (Ctxt.ofList [.llvm (.bitvec 64),.llvm (.bitvec 64)]) .pure (.llvm (.bitvec 64)) :=
  rewritePeephole_multi LLVMPlusRiscV ((fuel_def test_pep0_dce.val)) (loweringPass) test_pep0_dce.val
#eval! test_peep0
def test_peep0_cast_elimination := rewritePeephole_multi LLVMPlusRiscV (fuel_def test_peep0) (reconcile_cast_pass_llvm) test_peep0
#eval! test_peep0_cast_elimination
-- still need to find out why dead code does not get eliminated.
def test_pep0_dce1:= (DCE.dce' test_peep0_cast_elimination)
#eval! test_pep0_dce1
def test_pep0_dce_dce := (DCE.dce' test_pep0_dce.val)
#eval! test_pep0_dce_dce


/- experiment 02:
  first apply dead code elimination on the IR itself, then
  then perform the lowering of instructions where we have one operand
  then perform dead code elimination on this
  then peform the rest of the lowering pass
  then perform a cast reconconile pass
  then perform dead code elimination on -/
def pep0_dce_1:= (DCE.dce'  llvm00)
#eval! pep0_dce_1
def peep0_single_1 :  Com LLVMPlusRiscV (Ctxt.ofList [.llvm (.bitvec 64),.llvm (.bitvec 64)]) .pure (.llvm (.bitvec 64)) :=
  rewritePeephole_multi LLVMPlusRiscV (fuel_def llvm00) (loweringPassSingle) pep0_dce_1.val
#eval! peep0_single_1 -- lowers the sub instruction where two operands are the same.
def test_peep0_dce_1:= (DCE.dce' peep0_single_1)
#eval! test_peep0_dce_1
def peep0_1 :  Com LLVMPlusRiscV (Ctxt.ofList [.llvm (.bitvec 64),.llvm (.bitvec 64)]) .pure (.llvm (.bitvec 64)) :=
  rewritePeephole_multi LLVMPlusRiscV (13) (loweringPass) test_peep0_dce_1.val
#eval! peep0_1
def test_peep0_cast_elimination_1 := rewritePeephole_multi LLVMPlusRiscV (10) (reconcile_cast_pass_llvm) peep0_1
#eval! test_peep0_cast_elimination_1

/-testing on a second program without having the same operand as an input twice.
This is an example where I still have a cast in between the operations.
-/
def llvm01:=
      [LV|{
      ^bb0(%X : i64, %Y : i64):
      %1 = llvm.add %X, %Y : i64
      %2 = llvm.add %1, %Y : i64
      llvm.return %2 : i64
  }]

def pep0_dce_01:= (DCE.dce' llvm01)
#eval! pep0_dce_01
def peep0_single_01 :  Com LLVMPlusRiscV (Ctxt.ofList [.llvm (.bitvec 64),.llvm (.bitvec 64)]) .pure (.llvm (.bitvec 64)) :=
  rewritePeephole_multi LLVMPlusRiscV (fuel_def llvm01) (loweringPassSingle) pep0_dce_01.val
#eval! peep0_single_01 -- lowers the sub instruction where two operands are the same.
def test_peep0_dce_01:= (DCE.dce' peep0_single_01)
#eval! test_peep0_dce_01
def peep0_01 :  Com LLVMPlusRiscV (Ctxt.ofList [.llvm (.bitvec 64),.llvm (.bitvec 64)]) .pure (.llvm (.bitvec 64)) :=
  rewritePeephole_multi LLVMPlusRiscV (fuel_def (test_peep0_dce_01.val)) (loweringPass) test_peep0_dce_01.val
#eval! peep0_01
def test_peep0_cast_elimination_01 := rewritePeephole_multi LLVMPlusRiscV (10) (reconcile_cast_pass_llvm) peep0_01
#eval! test_peep0_cast_elimination_01
def test_peep01_deadcode_01 := (DCE.dce' test_peep0_cast_elimination_01)
#eval! test_peep01_deadcode_01
def test_peep01_deadcode_02 := (DCE.dce' test_peep01_deadcode_01.val)
#eval! test_peep01_deadcode_02
unsafe def test_peep01_dse_01 := (CSE.cse' test_peep01_deadcode_02.val)
#eval! test_peep01_dse_01 -- did apply
unsafe def test_peep01_last_01 := (DCE.dce' test_peep01_dse_01.val)
-- DIRECTLY GET A STACK OVERFLOW AND DO NOT UNDERSTAND WHY.
#eval! test_peep01_last_01.val


/-
Pipeline structure:
 DCE (avoid lowering unnecessary instructions, proven to be correct)
  ->
    lowerPassSingle (to lower instruction of the form, add X X )
        ->
          lowerPassFull (to lower any other instruction using two diffrent SSA variable inputs)
              ->
                DCE (to remove the llvm instructions)
                    ->
                      CSE (to remove cast when operand is used multiple times)
                        ->
                          DCE (to remove dead code introduced by the CSE)
                            ->
                              (next in my dreams: register allocation or removing the casts)
-/


unsafe def selectionPipe {Γl : List LLVMPlusRiscV.Ty} (prog : Com LLVMPlusRiscV (Ctxt.ofList Γl) .pure (.llvm (.bitvec 64))  ):=
  let initial_dead_code :=  (DCE.dce' prog).val; -- first we eliminate the inital inefficenices in the code.
  let lowerConst := (rewritePeephole_multi LLVMPlusRiscV (fuel_def initial_dead_code) (loweringPassConst) initial_dead_code);
  let lower_binOp_self := (rewritePeephole_multi LLVMPlusRiscV (fuel_def lowerConst) (loweringPassSingle) lowerConst); --then we lower all single one operand instructions.
  let remove_binOp_self_llvm := (DCE.dce' lower_binOp_self).val; -- then we eliminate first dead-code introdcued by the lowring the prev instructions.
  let lowering_all :=  rewritePeephole_multi LLVMPlusRiscV (fuel_def remove_binOp_self_llvm) (loweringPass) remove_binOp_self_llvm;
  let remove_llvm_instr := (DCE.dce' lowering_all).val;
  let reconcile_Cast := rewritePeephole_multi LLVMPlusRiscV (fuel_def remove_llvm_instr) (reconcile_cast_pass_llvm) remove_llvm_instr;
  let minimal_cast := (DCE.dce' reconcile_Cast).val; -- to do think of whether this makes a diff.
  --let minimal_cast := (DCE.dce' remove_dead_Cast).val; -- to do: unsrue why apply cast elimination twice
  let optimize_eq_cast := (CSE.cse' minimal_cast).val; -- this simplifies when an operand gets casted multiple times.
  let out := (DCE.dce' optimize_eq_cast).val;
  out
-- next step here would be to remove the casts.
-- i think cse does not yet match in the value of the immedates, therefore is pattern can't be recognized yet.

-- higher fuel apparently my fuel definiton was not enough.
unsafe def selectionPipeFuel100 {Γl : List LLVMPlusRiscV.Ty} (prog : Com LLVMPlusRiscV (Ctxt.ofList Γl) .pure (.llvm (.bitvec 64))  ):=
  let initial_dead_code :=  (DCE.dce' prog).val; -- first we eliminate the inital inefficenices in the code.
  let lowerConst := (rewritePeephole_multi LLVMPlusRiscV (100) (loweringPassConst) initial_dead_code);
  let lower_binOp_self := (rewritePeephole_multi LLVMPlusRiscV (100) (loweringPassSingle) lowerConst); --then we lower all single one operand instructions.
  let remove_binOp_self_llvm := (DCE.dce' lower_binOp_self).val; -- then we eliminate first dead-code introdcued by the lowring the prev instructions.
  let lowering_all :=  rewritePeephole_multi LLVMPlusRiscV (100) (loweringPass) remove_binOp_self_llvm;
  let remove_llvm_instr := (DCE.dce' lowering_all).val;
  let reconcile_Cast := rewritePeephole_multi LLVMPlusRiscV (100) (reconcile_cast_pass_llvm) remove_llvm_instr;
  let minimal_cast := (DCE.dce' reconcile_Cast).val; -- to do think of whether this makes a diff.
  --let minimal_cast := (DCE.dce' remove_dead_Cast).val; -- to do: unsrue why apply cast elimination twice
  let optimize_eq_cast := (CSE.cse' minimal_cast).val; -- this simplifies when an operand gets casted multiple times.
  let out := (DCE.dce' optimize_eq_cast).val;
  out
-- next step here would be to remove the casts.
-- i think cse does not yet match in the value of the immedates, therefore is pattern can't be recognized yet.

-- here we do not perform cse because cse is unsafe
 def selectionPipeFuel100Safe {Γl : List LLVMPlusRiscV.Ty} (prog : Com LLVMPlusRiscV (Ctxt.ofList Γl) .pure (.llvm (.bitvec 64))  ):=
  let initial_dead_code :=  (DCE.dce' prog).val; -- first we eliminate the inital inefficenices in the code.
  let lowerConst := (rewritePeephole_multi LLVMPlusRiscV (100) (loweringPassConst) initial_dead_code);
  let lower_binOp_self := (rewritePeephole_multi LLVMPlusRiscV (100) (loweringPassSingle) lowerConst); --then we lower all single one operand instructions.
  let remove_binOp_self_llvm := (DCE.dce' lower_binOp_self).val; -- then we eliminate first dead-code introdcued by the lowring the prev instructions.
  let lowering_all :=  rewritePeephole_multi LLVMPlusRiscV (100) (loweringPass) remove_binOp_self_llvm;
  let remove_llvm_instr := (DCE.dce' lowering_all).val;
  let reconcile_Cast := rewritePeephole_multi LLVMPlusRiscV (100) (reconcile_cast_pass_llvm) remove_llvm_instr;
  let minimal_cast := (DCE.dce' reconcile_Cast).val; -- to do think of whether this makes a diff.
  --let minimal_cast := (DCE.dce' remove_dead_Cast).val; -- to do: unsrue why apply cast elimination twice
  --let optimize_eq_cast := (CSE.cse' minimal_cast).val; -- this simplifies when an operand gets casted multiple times.
  let out := (DCE.dce' minimal_cast).val;
  out
/- problem at the moment here that it needs to be generic over the width of the input program,
so its not a function at the moment that is generic over program width -/
  def llvm002 := [LV| {
  ^bb0(%a : i64 , %b : i64 ):
    %v1 = llvm.mlir.constant 0 : i64
    %v3 = llvm.mlir.constant -1 : i64
    %v4 = llvm.sub %v3, %b : i64
    %v5 = llvm.add %v1, %v4 : i64
    %v6 = llvm.sub %v5, %b : i64
    %v7 = llvm.add %v6, %v4 : i64
    %v8 = llvm.sub %v7, %v6 : i64
    %v9 = llvm.add %v8, %v5 : i64
    %v10 = llvm.sub %v9, %v8 : i64
    %v11 = llvm.add %v10, %v9 : i64
    llvm.return %v11 : i64
  }]
unsafe def riscv_ssa_asm_002 := (selectionPipeFuel100 (llvm002))
#eval! riscv_ssa_asm_002

def llvm003 :=
  [LV| {
  ^bb0(%x : i64, %C : i64):
    %v2 = llvm.sub %x, %C : i64
    %v4 = llvm.sub %C, %v2 : i64
    %v5 = llvm.sub %v4, %x : i64
    llvm.return %v5 : i64
  }]

unsafe def riscv_ssa_asm_003 := (selectionPipeFuel100 (llvm003))
#eval! riscv_ssa_asm_003
/-

  let lowering_all :=  rewritePeephole_multi LLVMPlusRiscV (fuel_def remove_binOp_self_llvm) (loweringPass) remove_binOp_self_llvm;


-/
/- now will perform a scaling test-/
