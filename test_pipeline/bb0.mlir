{
    ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() {value = 20 : i64} : () -> i64
    %1 = "llvm.mlir.constant"() {value = 31 : i64} : () -> i64
    %2 = "llvm.ashr"(%arg0, %1) : (i64, i64) -> i64
    %3 = "llvm.and"(%2, %0) : (i64, i64) -> i64
    %4 = "llvm.add"(%3, %2) : (i64, i64) -> i64
    %5 = "llvm.add"(%4, %3) : (i64, i64) -> i64
    "llvm.return"(%5) : (i64) -> ()
}

