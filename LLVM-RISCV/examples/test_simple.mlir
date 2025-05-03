module attributes {dlti.dl_spec = #dlti.dl_spec<#dlti.dl_entry<f128, dense<128> : vector<2xi64>>, #dlti.dl_entry<f64, dense<64> : vector<2xi64>>, #dlti.dl_entry<f16, dense<16> : vector<2xi64>>, #dlti.dl_entry<i64, dense<[32, 64]> : vector<2xi64>>, #dlti.dl_entry<i16, dense<16> : vector<2xi64>>, #dlti.dl_entry<i32, dense<32> : vector<2xi64>>, #dlti.dl_entry<i1, dense<8> : vector<2xi64>>, #dlti.dl_entry<i8, dense<8> : vector<2xi64>>, #dlti.dl_entry<!llvm.ptr, dense<64> : vector<4xi64>>, #dlti.dl_entry<"dlti.endianness", "little">>} {
  llvm.func @gin(%arg0: i64) -> i64 {
    %0 = llvm.mlir.constant(31 : i64) : i64
    %1 = llvm.add %arg0, %arg0 : i64
    %2 = llvm.xor %1, %arg0  : i64
    %3 = llvm.mul %2, %2 : i64
    %4 = llvm.or %3, %1  : i64
    %5 = llvm.sub %4, %2 : i64
    %6 = llvm.xor %5, %arg0  : i64
    %7 = llvm.add %6, %1 : i64
    %8 = llvm.mul %7, %0 : i64
    %9 = llvm.or %8, %2  : i64
    %10 = llvm.sub %9, %6 : i64
    llvm.return %10 : i64
  }
  llvm.func @main(%arg0: i64) -> i64 {
    %0 = llvm.call @gin(%arg0) : (i64) -> i64
    %1 = llvm.add %0, %arg0 overflow<nsw> : i64
    llvm.return %1 : i64
  }
}
