
-- file where I sketch my worklfow and try to modell a rewrite across dialects in LLVM
-- and Riscv

-- the translation goal

theorem 




theorem shift_mul:
    [llvm(w)| {
  ^bb0(%X : _, %Y : _):
    %c1 = llvm.mlir.constant(1)
    %poty = llvm.shl %c1, %Y
    %r = llvm.mul %poty, %X
    llvm.return %r
  }] ⊑  [llvm(w)| {
  ^bb0(%X : _, %Y : _):
    %r = llvm.shl %X, %Y
    llvm.return %r
  }] := by
  simp_alive_peephole
  simp_alive_undef
  simp_alive_ops
  simp_alive_case_bash
  · simp
  · simp
