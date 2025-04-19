import SSA.Core.MLIRSyntax.EDSL
import RiscvDialect.RISCV64.Base

open MLIR AST Ctxt
open RISCV64

namespace RISCVExpr

def const {Γ : Ctxt _} (n : ℤ) : Expr RV64 Γ .pure .bv  :=
  Expr.mk
    (op := Op.const n)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .nil)
    (regArgs := HVector.nil)
-- this is to easily write IR by hand
-- alterantive would work :: Γ.Var .bv
def add {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bv) : Expr RV64 Γ .pure .bv  :=
  Expr.mk
    (op := Op.add)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

def sub {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bv) : Expr RV64 Γ .pure .bv  :=
  Expr.mk
    (op := Op.sub)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil) -- debug
    (regArgs := HVector.nil)

def and {Γ : Ctxt _} (e₁ e₂: Ctxt.Var Γ .bv) : Expr RV64 Γ .pure .bv  :=
  Expr.mk
    (op := Op.and)
    (eff_le := by constructor)
    (ty_eq := rfl)
    (args := .cons e₁ <| .cons e₂ .nil)
    (regArgs := HVector.nil)

end RISCVExpr
/-
  |.sra, regs, _  => RV64.RTYPE_pure64_RISCV_SRA (regs.getN 0 (by simp [DialectSignature.sig, signature]))  (regs.getN 1 (by simp [DialectSignature.sig, signature]))
  |.srai shamt, regs, _  => RV64.SHIFTIOP_pure64_RISCV_SRAI shamt  (regs.getN 0 (by simp [DialectSignature.sig, signature]))
-/

-- string representation of MLIR type into corresponding RISCV type
def mkTy : MLIR.AST.MLIRType φ → MLIR.AST.ExceptM RV64 RV64.Ty
  | MLIR.AST.MLIRType.undefined s => do
    match s with
    | "i64" => return .bv
    | _ => throw .unsupportedType
  | _ => throw .unsupportedType

--#eval mkTy (MLIR.AST.MLIRType.undefined "BitVec_64")

instance instTransformTy : MLIR.AST.TransformTy RV64 0 where
  mkTy := mkTy

#check Expr.mk
#check mkTy

def mkExpr (Γ : Ctxt _) (opStx : MLIR.AST.Op 0) :
  MLIR.AST.ReaderM (RV64) (Σ eff ty, Expr (RV64) Γ eff ty) := do
    match opStx.args with
    | []  => do
        let some att := opStx.attrs.getAttr "val"
          | throw <| .unsupportedOp s!"no attirbute in const {repr opStx}"
        match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .const (val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
    | v₁Stx::[] =>
       let ⟨ty₁, v₁⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₁Stx
        match ty₁, opStx.name with
        | .bv, "RV64.srai" => do
          let some att := opStx.attrs.getAttr "shamt"
             | throw <| .unsupportedOp s!"no attirbute in srai {repr opStx}"
          match att with
          | .int val ty => -- ides modell it as a list of 3 bools
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .srai (BitVec.ofInt 6 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.bclri" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in bclri {repr opStx}"
          match att with
          | .int val ty => -- ides modell it as a list of 3 bools
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .bclri (BitVec.ofInt 6 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.bexti" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in bexti {repr opStx}"
          match att with
          | .int val ty => -- ides modell it as a list of 3 bools
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .bexti (BitVec.ofInt 6 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.bseti" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in bseti {repr opStx}"
          match att with
          | .int val ty => -- ides modell it as a list of 3 bools
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .bseti (BitVec.ofInt 6 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.binvi" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in binvi {repr opStx}"
          match att with
          | .int val ty => -- ides modell it as a list of 3 bools
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .binvi (BitVec.ofInt 6 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.addiw" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in addiw {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .addiw (BitVec.ofInt 12 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
             -- .cons v₁ ::ₕ .nil,-- ask for what is this
              .nil --
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.lui" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in lui {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .lui (BitVec.ofInt 20 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
             -- .cons v₁ ::ₕ .nil,-- ask for what is this
              .nil --
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.auipc" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in auipc {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .auipc (BitVec.ofInt 20 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.slliw" => do
          let some att := opStx.attrs.getAttr "shamt"
            | throw <| .unsupportedOp s!"no attirbute in slliw {repr opStx}"
          match att with
          | .int val ty => -- ides modell it as a list of 3 bools
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .slliw (BitVec.ofInt 5 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.srliw" => do
          let some att := opStx.attrs.getAttr "shamt"
            | throw <| .unsupportedOp s!"no attirbute in slliw {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .srliw (BitVec.ofInt 5 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.sraiw" => do
          let some att := opStx.attrs.getAttr "shamt"
            | throw <| .unsupportedOp s!"no attirbute in sraiw {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .sraiw (BitVec.ofInt 5 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.slli" => do
          let some att := opStx.attrs.getAttr "shamt"
            | throw <| .unsupportedOp s!"no attirbute in slli{repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .slli (BitVec.ofInt 6 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.srli" => do
          let some att := opStx.attrs.getAttr "shamt"
            | throw <| .unsupportedOp s!"no attirbute in srli {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .srli (BitVec.ofInt 6 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
              .nil
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.addi" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in addi {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .addi (BitVec.ofInt 12 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
             -- .cons v₁ ::ₕ .nil,-- ask for what is this
              .nil --
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.slti" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in slti {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .slti (BitVec.ofInt 12 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
             -- .cons v₁ ::ₕ .nil,-- ask for what is this
              .nil --
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.sltiu" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in sltiu {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .sltiu (BitVec.ofInt 12 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
             -- .cons v₁ ::ₕ .nil,-- ask for what is this
              .nil --
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.andi" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in andi {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .andi (BitVec.ofInt 12 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
             -- .cons v₁ ::ₕ .nil,-- ask for what is this
              .nil --
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.ori" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in ori {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .ori (BitVec.ofInt 12 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
             -- .cons v₁ ::ₕ .nil,-- ask for what is this
              .nil --
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.xori" => do
          let some att := opStx.attrs.getAttr "imm"
            | throw <| .unsupportedOp s!"no attirbute in ori {repr opStx}"
          match att with
          | .int val ty =>
            let opTy@(.bv) ← mkTy ty -- ty.mkTy
            return ⟨.pure, opTy, ⟨
              .xori (BitVec.ofInt 12 val),
              by
              simp[DialectSignature.outTy, signature]
             ,
              by constructor,
              .cons v₁ <| .nil,
             -- .cons v₁ ::ₕ .nil,-- ask for what is this
              .nil --
            ⟩⟩
          | _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
        | .bv, "RV64.sext.b" =>
            return ⟨ .pure, .bv ,⟨ .sext.b, by rfl, by constructor,
               .cons v₁ <| .nil,
                .nil⟩⟩
        | .bv, "RV64.sext.h" =>
            return ⟨ .pure, .bv ,⟨ .sext.h, by rfl, by constructor,
               .cons v₁ <| .nil,
                .nil⟩⟩
        | .bv, "RV64.zext.h" =>
            return ⟨ .pure, .bv ,⟨ .zext.h, by rfl, by constructor,
               .cons v₁ <| .nil,
                .nil⟩⟩
        |_ , _ => throw <| .unsupportedOp s!"unsupported operation {repr opStx}"
    | v₁Stx::v₂Stx:: [] =>
        let ⟨ty₁, v₁⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₁Stx
        let ⟨ty₂, v₂⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ v₂Stx
        match ty₁, ty₂, opStx.name with
        | .bv, .bv, "RV64.rem" =>
          return ⟨.pure, .bv ,⟨ .rem, by rfl ,by constructor,
             .cons v₁ <| .cons v₂ <| .nil,
              .nil ⟩⟩
        | .bv, .bv, "RV64.ror" =>
          return ⟨.pure, .bv ,⟨ .ror, by rfl ,by constructor,
             .cons v₁ <| .cons v₂ <| .nil,
              .nil ⟩⟩
        | .bv, .bv, "RV64.rol" =>
          return ⟨.pure, .bv ,⟨ .rol, by rfl ,by constructor,
             .cons v₁ <| .cons v₂ <| .nil,
              .nil ⟩⟩
        | .bv, .bv, "RV64.remu" =>
          return ⟨.pure, .bv ,⟨ .remu, by rfl ,by constructor,
             .cons v₁ <| .cons v₂ <| .nil,
              .nil ⟩⟩
        | .bv, .bv, "RV64.sra" =>
          return ⟨.pure, .bv ,⟨ .sra, by rfl ,by constructor,
             .cons v₁ <| .cons v₂ <| .nil,
              .nil ⟩⟩
        | .bv, .bv, "RV64.addw" =>
          return ⟨.pure, .bv ,⟨ .addw, by rfl ,by constructor,
             .cons v₁ <| .cons v₂ <| .nil,
              .nil ⟩⟩
        | .bv , .bv , "RV64.subw" =>
              return ⟨ .pure, .bv ,⟨ .subw, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.sllw" =>
              return ⟨ .pure, .bv ,⟨ .sllw, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.srlw" =>
              return ⟨ .pure, .bv ,⟨ .srlw, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.sraw" =>
              return ⟨ .pure, .bv ,⟨ .sraw, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.add" =>
              return ⟨ .pure, .bv ,⟨ .add, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.or" =>
              return ⟨ .pure, .bv ,⟨ .or, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.xor" =>
              return ⟨ .pure, .bv ,⟨ .xor, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.sll" =>
              return ⟨ .pure, .bv ,⟨ .sll, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.srl" =>
              return ⟨ .pure, .bv ,⟨ .srl, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.sub" =>
              return ⟨ .pure, .bv ,⟨ .sub, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.slt" =>
              return ⟨ .pure, .bv ,⟨ .slt, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.sltu" =>
              return ⟨ .pure, .bv ,⟨ .sltu, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.and" =>
              return ⟨ .pure, .bv ,⟨ .and, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.czero.eqz" =>
              return ⟨ .pure, .bv ,⟨ .czero.eqz, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.czero.nez" =>
              return ⟨ .pure, .bv ,⟨ .czero.nez, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.bclr" =>
              return ⟨ .pure, .bv ,⟨ .bclr, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.bext" =>
              return ⟨ .pure, .bv ,⟨ .bext, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.binv" =>
              return ⟨ .pure, .bv ,⟨ .binv, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.bset" =>
              return ⟨ .pure, .bv ,⟨ .bset, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.rolw" =>
              return ⟨ .pure, .bv ,⟨ .rolw, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.rorw" =>
              return ⟨ .pure, .bv ,⟨ .rorw, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.mul" =>
            return ⟨ .pure, .bv ,⟨ .mul, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.mulu" =>
            return ⟨ .pure, .bv ,⟨ .mulu, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.mulh" =>
            return ⟨ .pure, .bv ,⟨ .mulh, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.mulhu" =>
            return ⟨ .pure, .bv ,⟨ .mulhu, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv , .bv , "RV64.mulhsu" =>
            return ⟨ .pure, .bv ,⟨ .mulhsu, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩

        | .bv , .bv , "RV64.mulw" => do -- (s : Bool)
          return ⟨ .pure, .bv ,⟨ .mulw, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv, .bv, "RV64.divw" =>
          return ⟨ .pure, .bv ,⟨ .divw, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv, .bv, "RV64.divwu" =>
            return ⟨ .pure, .bv ,⟨ .divwu, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv, .bv, "RV64.div" =>
            return ⟨ .pure, .bv ,⟨ .div, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv, .bv, "RV64.divu" =>
            return ⟨ .pure, .bv ,⟨ .divu, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv, .bv, "RV64.remw" =>
            return ⟨ .pure, .bv ,⟨ .remw, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩
        | .bv, .bv, "RV64.remwu" =>
            return ⟨ .pure, .bv ,⟨ .remw, by rfl, by constructor,
               .cons v₁ <| .cons v₂ <| .nil,
                .nil⟩⟩


        | _, _ , _ => throw <| .unsupportedOp s!"type mismatch  for 2 reg operation  {repr opStx}"
    | _ => throw <| .unsupportedOp s!"wrong number of arguemnts, more than 2 arguemnts  {repr opStx}"

instance : MLIR.AST.TransformExpr (RV64) 0 where
  mkExpr := mkExpr

def mkReturn (Γ : Ctxt _) (opStx : MLIR.AST.Op 0) : MLIR.AST.ReaderM (RV64)
    (Σ eff ty, Com RV64 Γ eff ty) :=
  if opStx.name == "return"
  then match opStx.args with
  | vStx::[] => do
    let ⟨ty, v⟩ ← MLIR.AST.TypedSSAVal.mkVal Γ vStx
    return ⟨.pure, ty, Com.ret v⟩
  | _ => throw <| .generic s!"Ill-formed return statement (wrong arity, expected 1, got {opStx.args.length})"
  else throw <| .generic s!"Tried to build return out of non-return statement {opStx.name}"


instance : MLIR.AST.TransformReturn (RV64) 0 where
  mkReturn := mkReturn


open Qq MLIR AST Lean Elab Term Meta in
elab "[RV64_com| " reg:mlir_region "]" : term => do
  SSA.elabIntoCom reg q(RV64)
