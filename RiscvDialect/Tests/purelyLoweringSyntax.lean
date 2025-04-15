import RiscvDialect.Instructions.instructionSelection


open toRISCV
open RV64
open InstCombine (LLVM)

/-
actuall llvm ir code:

  llvm.func local_unnamed_addr @add_64(%arg0: i64 {llvm.noundef}, %arg1: i64 {llvm.noundef}) -> i64 attributes {frame_pointer = #llvm.framePointerKind<"non-leaf">, memory = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none>, no_inline, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "ssp", ["uwtable", "1"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "apple-m1"]], target_cpu = "apple-m1", target_features = #llvm.target_features<["+aes", "+altnzcv", "+ccdp", "+ccidx", "+complxnum", "+crc", "+dit", "+dotprod", "+flagm", "+fp-armv8", "+fp16fml", "+fptoint", "+fullfp16", "+jsconv", "+lse", "+neon", "+pauth", "+perfmon", "+predres", "+ras", "+rcpc", "+rdm", "+sb", "+sha2", "+sha3", "+specrestrict", "+ssbs", "+v8.1a", "+v8.2a", "+v8.3a", "+v8.4a", "+v8a", "+zcm", "+zcz"]>, will_return} {
    %0 = llvm.add %arg1, %arg0 overflow<nsw> : i64
    llvm.return %0 : i64
  }
-/
def realLLVMexample :=
    --llvm.func local_unnamed_addr @add_64(%arg0: i64 {llvm.noundef}, %arg1: i64 {llvm.noundef}) -> i64 attributes {frame_pointer = #llvm.framePointerKind<"non-leaf">, memory = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = none>, no_unwind, passthrough = ["mustprogress", "nofree", "norecurse", "nosync", "ssp", ["uwtable", "1"], ["no-trapping-math", "true"], ["stack-protector-buffer-size", "8"], ["target-cpu", "apple-m1"]], target_cpu = "apple-m1", target_features = #llvm.target_features<["+aes", "+altnzcv", "+ccdp", "+ccidx", "+complxnum", "+crc", "+dit", "+dotprod", "+flagm", "+fp-armv8", "+fp16fml", "+fptoint", "+fullfp16", "+jsconv", "+lse", "+neon", "+pauth", "+perfmon", "+predres", "+ras", "+rcpc", "+rdm", "+sb", "+sha2", "+sha3", "+specrestrict", "+ssbs", "+v8.1a", "+v8.2a", "+v8.3a", "+v8.4a", "+v8a", "+zcm", "+zcz"]>, will_return} {
    [llvm(64)| {
      ^bb0 (%arg0: i64 , %arg1: i64):
    %0 = llvm.add %arg1, %arg0 overflow<nsw> : i64
    llvm.return %0 : i64
    }]

def realRISCVadd :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "RV64.add" (%Y, %X) : (!i64, !i64) -> (!i64)
    "return" (%v1) : (!i64, !i64) -> ()
  }]



def loweringrealLLVMexample :  loweringLLVMtoRISCV realLLVMexample = some (realRISCVadd) := by native_decide
-- now just need to revert this and rewrite it into the IR again

def optimizedCode: Com RV64 [.bv] .pure .bv := rewritePeepholeAt rewrite_add0 1 riscv_const_add
-- now try run rewritting pass on the generated riscv-code
def applyPeepholeOptimizationOnRewritten : some (optimizedCode) = some rhs := by native_decide
