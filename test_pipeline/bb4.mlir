{
  ^bb0(%arg0: i64):
    %c1 = "llvm.mlir.constant"() {value = 1 : i64} : () -> i64
    %c3 = "llvm.mlir.constant"() {value = 2 : i64} : () -> i64
    %c7 = "llvm.mlir.constant"() {value = 0 : i64} : () -> i64
    %c15 = "llvm.mlir.constant"() {value = 2 : i64} : () -> i64
    %c32 = "llvm.mlir.constant"() {value = 1 : i64} : () -> i64
    %c64 = "llvm.mlir.constant"() {value = 2 : i64} : () -> i64

    %s1 = "llvm.ashr"(%arg0, %c3) : (i64, i64) -> i64
    %s2 = "llvm.shl"(%arg0, %c7) : (i64, i64) -> i64

    %b1 = "llvm.and"(%s1, %c15) : (i64, i64) -> i64
    %b2 = "llvm.or"(%b1, %s2) : (i64, i64) -> i64
    %b3 = "llvm.xor"(%b2, %arg0) : (i64, i64) -> i64

    %a1 = "llvm.add"(%b3, %s1) : (i64, i64) -> i64
    %a2 = "llvm.mul"(%a1, %c3) : (i64, i64) -> i64
    %a3 = "llvm.sub"(%a2, %s2) : (i64, i64) -> i64
    
    %m1 = "llvm.and"(%a3, %c32) : (i64, i64) -> i64
    %m2 = "llvm.shl"(%m1, %c1) : (i64, i64) -> i64

    %c = "llvm.or"(%m2, %a1) : (i64, i64) -> i64
    %r1 = "llvm.sdiv"(%c, %c3) : (i64, i64) -> i64
    %r2 = "llvm.srem"(%r1, %c7) : (i64, i64) -> i64

    %res = "llvm.add"(%r2, %c64) : (i64, i64) -> i64

    "llvm.return"(%res) : (i64) -> ()
}
