import SSA.Projects.InstCombine.LLVM.Parser
import Cli
import RiscvDialect.LLVMRiscv.pipeline
/-
goal modify it to parse it as a hybrid dialect operation  -/
-- keep in mind to also modify the lakefile !
open LLVMRiscV

def runMainCmd1 (args : Cli.Parsed) : IO UInt32 := do
  let fileName := args.positionalArg! "file" |>.as! String
  let icom? ← parseComFromFile fileName
  match icom? with
    | none => return 1
    | some (Sigma.mk _Γ icom) => do
      let icom'' := icom.snd.snd
      let icom_output := (icom'')
      IO.println s!"OK: parsed"
      IO.println s!"{repr icom_output}"
      return 0

open MLIR AST InstCombine
def regionTransform2 (region : Region 0) : Except ParseError
  (Σ (Γ' : Ctxt LLVMPlusRiscV.Ty ) (eff : EffectKind) (ty : LLVMPlusRiscV.Ty ), Com LLVMPlusRiscV Γ' eff ty) :=
    let res := mkCom (d:= LLVMPlusRiscV) region
    match res with
      | Except.error e => Except.error s!"Error:\n{reprStr e}"
      | Except.ok res => Except.ok res

-- parses it as a hybrid com, if want to parse as llvm instcombine the use parse1
def parseComFromFile2 (fileName : String) :
 IO (Option (Σ (Γ' :  Ctxt LLVMPlusRiscV.Ty ) (eff : EffectKind) (ty :  LLVMPlusRiscV.Ty), Com LLVMPlusRiscV Γ' eff ty)) := do
 parseRegionFromFile fileName regionTransform2


def verbose_flag (fileName : String ) : IO UInt32 := do
      let icom? ← parseComFromFile fileName
      match icom? with
      | none => return 1
      | some (Sigma.mk _Γ icom) => do
      IO.println "Flag `--verbose` was set."
      IO.println s!"{repr icom}" -- we print everything, meaning effect, return type and com
      return 0

def passriscv64 (fileName : String) : IO UInt32 := do
    let icom? ← parseComFromFile2 fileName
    match icom? with
    | none => IO.println s!"wellformed passriscv64" return 1
    | some (Sigma.mk _Γ ⟨eff, ⟨retTy, c⟩⟩) =>
      match eff with
      | EffectKind.pure =>
        match retTy with
        | Ty.llvm (Ty.bitvec 64) =>
          -- IO.println "DEBUG : Flag `--passriscv64` was set."
      -- Now that we matched eff and retTy, we can safely assert types.
          let lowered :=  selectionPipeFuel100Safe c -- here we effectivly apply the lowering
          --let lowered1 :=  selectionPipeFuel100Safe c
          --IO.println s!"{lowered.denote  == lowered1.denote }"
          IO.println s!"{repr lowered}"
          return 0
        | _ =>
        IO.println s!" debug: WRONG RETURN TYPE : expected Ty.llvm (Ty.bitvec 64) "
        return 2
      | _ =>
      IO.println s!" debug: WRONG EFFECT KIND : expected pure program "
      return 3

def peephole (fileName : String) : IO UInt32 := do
    let icom? ← parseComFromFile2 fileName
    match icom? with
    | none => IO.println s!"debug 00" return 1
    | some (Sigma.mk _Γ ⟨eff, ⟨retTy, c⟩⟩) =>
      match eff with
      | EffectKind.pure =>
        match retTy with
        | Ty.llvm (Ty.bitvec 64) =>
      -- Now that we matched eff and retTy, we can safely assert types.
          let lowered :=  selectionPipeFuel100Safe c -- here we effectivly apply the lowering
          let lowered1 :=  selectionPipeFuel100Safe c
          IO.println s!"{lowered == lowered1 }" -- goal would be a denotation check
          return 0
        | _ =>
        IO.println s!" debug: WRONG RETURN TYPE : expected Ty.llvm (Ty.bitvec 64) "
        return 2
      | _ =>
      IO.println s!" debug: WRONG EFFECT KIND : expected pure program "
      return 3

def wellformed (fileName : String ) : IO UInt32 := do
    let icom? ← parseComFromFile fileName
    match icom? with
    | none => IO.println s!"wellformed debug" return 1
    | some (Sigma.mk _Γ ⟨_eff, ⟨_retTy, c⟩⟩) => do
      IO.println s!"{repr c}"
      return 0

-- to do : factor it out to indivdual function calls which is cleaner.
def runMainCmd2 (args : Cli.Parsed) : IO UInt32 := do
  let fileName := args.positionalArg! "file" |>.as! String
  if args.hasFlag "verbose" then -- in this case we just mirror the llvm program again and checked that it is wellformed.
    let code ← verbose_flag fileName
    return code
  if args.hasFlag "passriscv64" then
    let code ← passriscv64 fileName
    return code
  if args.hasFlag "peephole" then
    IO.println s!"in peephole"
    let code ← peephole fileName
    return code
  else
    IO.println s!" no flag passed hence just check wellformedness "
    let code ← wellformed fileName
    return code

/-- icom : (fun Γ' => (eff : EffectKind) × (ty : LLVMPlusRiscV.Ty) × Com LLVMPlusRiscV Γ' eff ty) _Γ-/
 def mainCmd := `[Cli|
    opt VIA runMainCmd2;
    "opt: apply verified rewrites"
    FLAGS:
      verbose; "Declares a flag `--verbose`. This is the description of the flag."
      passriscv64; "Declares a flag `--pass-riscv64`. This applies a lowering pass to RISC-V 64"
      peephole; "Declares a flag `--peephole`. This runs a verified peephole optimization pass on top of the RiscV SSA assembly."
    ARGS:
      file: String; "Input filename"
    ]

def main (args : List String): IO UInt32 :=
  mainCmd.validate args
