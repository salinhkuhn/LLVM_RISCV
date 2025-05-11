
import RiscvDialect.LLVMRiscv.LLVMAndRiscV
open LLVMRiscV

/-!
This file contains simple, small test cases to check wether the hybrid dialect parses
-/

-- return parsing works for RISC-V
def RISCVReturn := [LV|{
  ^entry (%0 : !i64 ):
  "ret" (%0) : ( !i64 ) -> ()
}]
#check RISCVReturn

def LLVMReturn :=
  [LV| {
  ^bb0(%X : i64, %Y : i64) :
   llvm.return %X : i64
  }]
#check LLVMReturn

/- ## test add -/
def llvm_add:=
  [LV| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add   %X, %Y : i64
      llvm.return %v1 : i64
  }]
#check llvm_add


def RISCV_add_pretty := [LV|{
  ^entry (%0: !i64):
    %1 =  add %0, %0 : !i64
          ret %1 : !i64
}]

def RISCV_add_unpretty := [LV| {
  ^entry (%0: !i64):
    %1 = "add" (%0, %0) : (!i64, !i64) -> (!i64)
         "ret" (%1) : (!i64) -> ()
}]

/- ## test cases with disjoint, nsw and exact flags -/
-- to d0

def or_disjoint_flag_test := [LV| {
  ^entry (%0: i64):
    %1 = llvm.or disjoint %0, %0 :  i64
    "llvm.return" (%1) : (i64) -> ()
}]


def add_flag_test_both := [LV| {
  ^entry (%0: i64):
    %1 = llvm.add %0, %0 overflow<nsw, nuw> : i64
    "llvm.return" (%1) : (i64) -> ()
}]

def add_flag_test := [LV| {
  ^entry (%0: i64):
    %1 = llvm.add %0, %0 overflow<nsw> : i64
    "llvm.return" (%1) : (i64) -> ()
}]
/- ## larger test cases  -/

  def llvm_const_add_neg_add:=
      [LV|{
      ^bb0(%X : i64):
      %v1 = llvm.mlir.constant 123848392 : i64
      %v2 = llvm.add %X, %v1 : i64
      %v3 = llvm.mlir.constant 0 :  i64
      %v4 = llvm.sub %v3, %X : i64
      %v = llvm.add %v2, %v1 : i64
      llvm.return %v : i64
  }]
  #check llvm_const_add_neg_add

  def riscv_const_add_neg_add_pretty :=
      [LV| {
      ^bb0(%X : !i64):
      %v1 = li (123848392) : !i64
      %v2 = add %X, %v1 : !i64
      %v3 = li (0) : !i64
      %v4 = sub %v3, %X : !i64
      %v = add %v2, %v1 : !i64
      ret %v : !i64
  }]
#check riscv_const_add_neg_add_pretty

  def riscv_const_add_neg_add_unpretty :=
  [LV| {
      ^bb0(%X : !i64):
      %v1 = "li" () { imm = 123848392 : !i64 } : (!i64, !i64) -> (!i64)
      %v2 = "add" (%X, %v1) : (!i64, !i64) -> (!i64)
      %v3 = "li" () { imm = 0 : !i64 } : (!i64, !i64) -> (!i64)
      %v4 = "sub" (%v3, %X) : (!i64, !i64) -> (!i64)
      %v = "add" (%v2, %v1) : (!i64, !i64) -> (!i64)
      "ret" (%v) : (!i64, !i64) -> ()
  }]
#check riscv_const_add_neg_add_unpretty
