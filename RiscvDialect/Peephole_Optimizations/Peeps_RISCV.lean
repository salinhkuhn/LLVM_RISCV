import RiscvDialect.LLVMRiscv.InstructionSelection.all

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V

def _test1 := [LV| {
    ^entry (%r1: i64, %r2: i64,  %r3: i64,  %r4: i64, %r5: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r1) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r2) : (i64) -> !i64
      %x3 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r3) : (i64) -> !i64
      %x4 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r4) : (i64) -> !i64
      %x5 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r5) : (i64) -> !i64
      %res = mul  %x1, %x2 : !i64
      %res1= mul  %x2, %x3 : !i64
      %res2= mul  %x3, %x3 : !i64
      %res3= mul  %x3, %x3 : !i64
      %y= "builtin.unrealized_conversion_cast.riscvToLLVM" (%res) : (!i64) -> (i64)
      llvm.return %y : i64
  }]
def _test2 := [LV| {
    ^entry (%r1: i64, %r2: i64,  %r3: i64,  %r4: i64, %r5: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r1) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r2) : (i64) -> !i64
      %x3 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r3) : (i64) -> !i64
      %x4 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r4) : (i64) -> !i64
      %x5 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r5) : (i64) -> !i64
      %res = mul  %x1, %x2 : !i64
      %y= "builtin.unrealized_conversion_cast.riscvToLLVM" (%res) : (!i64) -> (i64)
      llvm.return %y : i64
  }]



def _test2_input1 : Com  LLVMPlusRiscV [.riscv (.bv), .riscv (.bv),  .riscv (.bv) ] .pure (.riscv (.bv))  := [LV| {
    ^entry (%x1: !i64, %x2: !i64,  %x3: !i64 ):
      --%x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r1) : (i64) -> !i64
      --%x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r2) : (i64) -> !i64
      %imm = li (0) : !i64
      ret %imm : !i64
      --%y= "builtin.unrealized_conversion_cast.riscvToLLVM" (%res) : (!i64) -> (i64)
      --llvm.return %y : i64
  }]


--def test2 : PeepholeRewrite LLVMRiscV [Ty.riscv (.bv) , Ty.riscv (.bv),Ty.riscv (.bv)] :=

def test2 : PeepholeRewrite LLVMPlusRiscV [.llvm (.bitvec 64) , .llvm (.bitvec 64),.llvm (.bitvec 64), .llvm (.bitvec 64), .llvm (.bitvec 64)] (.llvm (.bitvec 64)) :=
  {lhs := _test1 , rhs := _test2 ,
    correct :=  by
      unfold _test2 _test1
      simp_peephole
      intro e e1 e3
      simp
  }




/-

def _test2_input2 := [LV| {
    ^entry (%r1: i64, %r2: i64,  %r3: i64,  %r4: i64, %r5: i64 ):
      --%x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r1) : (i64) -> !i64
      --%x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r2) : (i64) -> !i64
      --%x3 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r3) : (i64) -> !i64
      --%x4 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r4) : (i64) -> !i64
      --%x5 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r5) : (i64) -> !i64
      %imm = li (0) : !i64
      %res = mul  %x1, %imm: !i64
      %res1= mul  %x2, %x3 : !i64
      %res2= mul  %x3, %x3 : !i64
      %res3= mul  %x3, %x3 : !i64
      --%y= "builtin.unrealized_conversion_cast.riscvToLLVM" (%res) : (!i64) -> (i64)
      llvm.return %y : i64
  }]

-/
