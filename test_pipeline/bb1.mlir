{
  ^bb0(%arg0: i64):
    %c1 = "llvm.mlir.constant"() {value = 1 : i64} : () -> i64
    %c2 = "llvm.mlir.constant"() {value = 2 : i64} : () -> i64
    %x1 = "llvm.add"(%arg0, %c1) : (i64, i64) -> i64
    %x2 = "llvm.add"(%x1, %c2) : (i64, i64) -> i64
    %x3 = "llvm.shl"(%x2, %c1) : (i64, i64) -> i64
    %x4 = "llvm.sub"(%x3, %x1) : (i64, i64) -> i64
    %x5 = "llvm.add"(%x4, %x2) : (i64, i64) -> i64
    "llvm.return"(%x5) : (i64) -> ()
}
