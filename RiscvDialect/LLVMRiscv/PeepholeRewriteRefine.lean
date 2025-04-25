import SSA.Core.MLIRSyntax.EDSL
import SSA.Core.Framework
import SSA.Core.Util
import SSA.Core.Util.ConcreteOrMVar
import SSA.Projects.InstCombine.ForStd
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.Tactic
import RiscvDialect.LLVMRiscv.llvm_riscv

open LLVM
open llvm.riscv
/-!
## RiscvPeepholeRewriteRefine
This file contains the definition of the `RiscvPeepholeRewriteRefine`structure.
The strucutre serves as an bundle for the rhs, lhs and the corresponding correctness proof.
-/

-- variable (d : Dialect) [DialectSignature d] [TyDenote d.Ty] [DialectDenote d] [Monad d.m] in
structure RiscVPeepholeRewriteRefine (Γ : Ctxt Ty) where
  lhs : Com llvm.riscv Γ .pure Ty.bitvec
  rhs : Com llvm.riscv Γ .pure Ty.bitvec
  correct : ∀ V, BitVec.Refinement (lhs.denote V : Option _) (rhs.denote V : Option _)

-- TO DO: think of this on a diffrent level maybe directly between two programs instead of requring the same type


/--
##  Wrapper for peephole rewriter
-/
def RiscVPeepholeRewriteRefine.toPeepholeUNSOUND (self : RiscVPeepholeRewriteRefine Γ) : PeepholeRewrite llvm.riscv Γ .bitvec :=
  {
    lhs := self.lhs
    rhs := self.rhs
    correct := by sorry
  }
