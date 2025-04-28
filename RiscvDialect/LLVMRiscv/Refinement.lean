
import RiscvDialect.LLVMRiscv.LLVMAndRiscV

open LLVMRiscV
/-!
This file contains the defintion of the Peephole Rewrite structure for LLVM and RISCV.
The LLVMPeepholeRewrite structure is leveraged to lower LLVM program to a RISCV program where we insert unrealized conversion cast
from LLVM to RISCV and eliminate them in a subsequent pass to completely lower the program.
-/
structure LLVMPeepholeRewriteRefine (Γ : Ctxt Ty) where
  lhs : Com LLVMPlusRiscV Γ .pure (Ty.llvm (.bitvec 64))
  rhs : Com LLVMPlusRiscV Γ .pure (Ty.llvm (.bitvec 64))
  correct : ∀ V, BitVec.Refinement (lhs.denote V : Option _) (rhs.denote V : Option _)

structure RiscVPeepholeRewriteRefine1 (Γ : Ctxt Ty) where
  lhs : Com LLVMPlusRiscV Γ .pure (Ty.riscv (.bv))
  rhs : Com LLVMPlusRiscV Γ .pure (Ty.riscv (.bv))
  correct : ∀ V, BitVec.Refinement (lhs.denote V : Option _) (rhs.denote V : Option _)
