{
  ^bb0(%arg0: i64):
    %mask = "llvm.mlir.constant"() {value = 2 : i64} : () -> i64
    %shift = "llvm.mlir.constant"() {value = 1 : i64} : () -> i64
    %x1 = "llvm.and"(%arg0, %mask) : (i64, i64) -> i64
    %x2 = "llvm.shl"(%x1, %shift) : (i64, i64) -> i64
    %x3 = "llvm.or"(%x2, %arg0) : (i64, i64) -> i64
    %x4 = "llvm.sub"(%x3, %x1) : (i64, i64) -> i64
    "llvm.return"(%x4) : (i64) -> ()
}
