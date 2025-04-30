import RiscvDialect.LLVMRiscv.LLVMAndRiscV
import RiscvDialect.LLVMRiscv.Refinement
import Lean

open LLVMRiscV
open RV64Semantics -- needed to use RISC-V semantics in simp tactic
open InstCombine(LLVM) -- analog to RISC-V

/-
Disabled due to simproc implementation not being re-evaluated correctly
on Lean version "4.20.0-nightly-2025-04-21" -/
set_option Elab.async false

  --  (Ctxt.Valuation.nil::ᵥe) (Ctxt.Var.last [] (Ty.llvm (InstCombine.MTy.bitvec 64)))
@[simp_denote]
private theorem valuation_var_last_eq.lemma {Ty : Type} [TyDenote Ty] {Γ : Ctxt Ty} {t : Ty} {s : Γ.Valuation} {x : TyDenote.toType t} : (s.snoc x) (Ctxt.Var.last Γ t) = x := by
  rfl

#check Ctxt.Valuation.snoc


/-! # Instruction lowering patterns
    This file contains a collection of instruction lowerings that are performed by
    LLVM and make explicit what is performed by the LLVM backkend.
     -/
/-
f: Ctxt.Valuation.snoc, xs: [Ty,
 instTyDenoteTyLLVMPlusRiscV,
 [],
 Ty.llvm (InstCombine.Ty.bitvec 64),
 Ctxt.Valuation.nil,
 e,
 Ty.llvm (InstCombine.Ty.bitvec 64),
 Ctxt.Var.last [] (Ty.llvm (InstCombine.MTy.bitvec 64))]
-/
open Lean Meta Elab in
simproc [simp_denote] valuation_var_last_eq ((Ctxt.Valuation.snoc _ _) (Ctxt.Var.last _ _)) := fun e => do
  -- logInfo m!"Matched (Valuation.snoc s x) (Ctxt.Var.last Γ t) with {e}"
  let (_f, xs) := e.getAppFnArgs
  -- logInfo m!"f: {f}, xs: {xs}"
  let ty := xs[0]!
  let s := xs[4]!
  let x := xs[xs.size - 1 - 2]!
  -- logInfo m!"x: {x}"
  -- TODO: @alexkeizer, don't kill me for this :D I was lazy, so I just write down the full implicit match.
  -- We should probably decide which arguments are implicit, and then only pass these as explicit args.
  let proof ← mkAppOptM ``valuation_var_last_eq.lemma #[.some ty, .none, .none, .none, .some s, .some x]
  return .visit {
    expr := x,
    -- proof? := ← mkSorry (← mkEq x rhs) .true -- TODO: replace with call to valuation_var_last_eq.lemma.
    proof? := proof
  }
  -- let_expr ((Ctxt.Valuation.snoc _V x) (Ctxt.Var.last _ _)) := x

  -- let args ←
  -- let_expr ((Ctxt.Valuation.snoc _V x) (Ctxt.Var.last _ _)) := x




-- open Lean Meta Elab in
-- simproc [simp_denote] valuation_var_last_eq ((Ctxt.Valuation.snoc _ _) (Ctxt.Var.last _ _)) := fun e => do
--   let_expr Ctxt.Valuation.snoc Ty instDenote Γ t s x _v := e
--     | return .continue
--   return .visit {
--     expr := x,
--     proof? := some <| mkAppN (mkConst ``valuation_var_last_eq.lemma) #[Ty, instDenote, Γ, t, s, x]
--   }


theorem riscVArgsFromHybrid_nil_eq : riscvArgsFromHybrid (HVector.nil) = HVector.nil := rfl

-- LLVMRiscV.llvmArgsFromHybrid {tys : List LLVM.Ty} :
--   @HVector Ty (@TyDenote.toType Ty instTyDenoteTyLLVMPlusRiscV) (@List.map LLVM.Ty Ty Ty.llvm tys) →
--     @HVector LLVM.Ty (@TyDenote.toType LLVM.Ty InstCombine.instTyDenoteTy) tys
set_option pp.explicit true in
#check llvmArgsFromHybrid
#check HVector.cons
#synth Lean.ToExpr (List Lean.Expr)

#check Lean.instToExprListOfToLevel


open Lean Meta Elab in
/-- Convert a `List Expr` into an `Expr` by building calls to `List.nil` and `List.cons`.
Note that the `ToExpr` instance of `List` is insufficient, since it perform a *deep expression cast*,
where it converts any `List α` where `[ToExpr α]` into a `List Expr`. So, when given a list of expressions, like [.const Nat],
instead of building `[Nat]`, it builds `[Lean.Expr.Const ``Nat]` (i.e.., it seralizes the `Expr` as well!).
Instead, we want a shallow serialization, where we just build `List.cons (.const Nat) List.nil`.
-/
def listExprToExprShallow (type : Option Expr) : List Expr → MetaM Expr
| .nil => mkAppOptM ``List.nil #[type]
| .cons x xs => do mkAppOptM ``List.cons #[type, x, ← listExprToExprShallow type xs]

open Lean Meta Elab in
#check Lean.Environment

def f (n : Nat) : Bool := n % 2 == 0

def g : ∀ (_ : Nat), Bool := fun n => n % 2 == 0
def h : ∀ (w : Nat), BitVec w  :=
  -- | value
  fun (w : Nat) => 0#w

def h' : (w : Nat) → BitVec w  :=
  -- | value
  fun (w : Nat) => 0#w

-- let x := xdef in rest <-> (fun x => rest) xdef

/-#
Let versus Lambda in DTT (dependent type theory)
namespace LetVersusLam
inductive Matrix : Nat → Nat → Type where
| id : (n : Nat) → Matrix n n

def f (n : Nat) : Matrix n n :=
  let m := n
  let out : Matrix m n := Matrix.id n -- n : Nat, m : Nat, m = n |- Matrix.id n is well-typed
  out

def f' (n : Nat) : Matrix n n :=
  (fun m =>
    -- n : Nat, m : Nat |- Matrix.id n is well typed
    let out : Matrix m n := Matrix.id n
    out) n
end LetVersusLam
-/

#eval show String from toString (`Nat.Abs)

@[simp_denote]
def llvmArgsFromHybrid_nil_eq :
  (llvmArgsFromHybrid HVector.nil) = HVector.nil := rfl

def llvmArgsFromHybrid_cons_eq.lemma {ty  : LLVM.Ty} {tys : List LLVM.Ty}
    (x : TyDenote.toType (LLVMRiscV.Ty.llvm ty))
    (xs : HVector TyDenote.toType (tys.map LLVMRiscV.Ty.llvm)) :
  (llvmArgsFromHybrid (tys := ty :: tys) (HVector.cons x xs)) =
  HVector.cons (f := TyDenote.toType) (a := ty) (as := tys) x (llvmArgsFromHybrid xs)
   := rfl


open Lean Meta Elab in
/-- Extract out the raw LLVM type from the. -/
def extractLLVMTy (x : Expr) : SimpM Expr := do
  let_expr Ty.llvm xRealTy := (← reduce x)
    | throwError m! "expected type of {x} to be `Ty.llvm _`, but got {x}"
  return xRealTy

open Lean Meta Elab in
simproc [simp_denote] llvmArgsFromHybrid_cons_eq (llvmArgsFromHybrid _) := fun e => do
  let_expr llvmArgsFromHybrid _ lhs := e
    | throwError m!"unable to find llvmArgsFromHybrid in {e}"
  let_expr HVector.cons _α _f as a x xs := lhs
    | throwError m!"unable to find HVector.cons in {lhs}"
  let xRealTy ← extractLLVMTy a
  let some (_, xsRealTys) := Expr.listLit? (← reduce as)
    | return .continue
  let xsRealTys ←  xsRealTys.mapM extractLLVMTy

  logInfo m!"found (llvmArgsFromHybrid (HVector.cons ({x} : {xRealTy}) ({xs} : {xsRealTys})"
  let llvmTypeType := mkApp (mkConst ``Dialect.Ty []) (mkConst ``InstCombine.LLVM [])
  let xsRealTys ← listExprToExprShallow (.some llvmTypeType) xsRealTys

  logInfo m!"calling {``llvmArgsFromHybrid_cons_eq.lemma} with {xRealTy}, {xsRealTys}, {x}, {xs}"
  logInfo m!"XXXX"
  let proof := mkAppN (mkConst ``llvmArgsFromHybrid_cons_eq.lemma []) #[xRealTy, xsRealTys, x, xs]
  logInfo m!"YYYY"
  logInfo m!"built proof {proof}"
  let proof ← reduce proof
  logInfo m!"reduced proof to {proof}"
  let eq ← reduce (← inferType proof)
  logInfo m!"reduced type of proof (i.e. the equality) to {eq}"
  let .some (_ty, _lhs, rhs) := eq.eq?
    | throwError "unable to reduce application of 'llvmArgsFromHybrid_cons_eq.lemma' to an equality, only reduced to '{eq}'."
  logInfo m!"final right-hand-side of equality is: {rhs}"
  return .visit {
    expr := rhs,
    proof? := .some proof
  }

@[simp_denote]
def riscvArgsFromHybrid_nil_eq :
  (riscvArgsFromHybrid HVector.nil) = HVector.nil := rfl

def riscvArgsFromHybrid_cons_eq.lemma {ty  : RISCV64.RV64.Ty} {tys : List RISCV64.RV64.Ty}
    (x : TyDenote.toType (LLVMRiscV.Ty.riscv ty))
    (xs : HVector TyDenote.toType (tys.map LLVMRiscV.Ty.riscv)) :
  (riscvArgsFromHybrid (tys := ty :: tys) (HVector.cons x xs)) =
  HVector.cons (f := TyDenote.toType) (a := ty) (as := tys) x (riscvArgsFromHybrid xs)
   := rfl

open Lean Meta Elab in
/-- Extract out the raw LLVM type from the. -/
def extractRiscvTy (x : Expr) : SimpM Expr := do
  let_expr Ty.riscv xRealTy := (← reduce x)
    | throwError m! "expected type of {x} to be `Ty.riscv _`, but got {x}"
  return xRealTy


open Lean Meta Elab in
simproc [simp_denote] riscvArgsFromHybrid_cons_eq (riscvArgsFromHybrid _) := fun e => do
  let_expr riscvArgsFromHybrid _ lhs := e
    | throwError m!"unable to find riscvArgsFromHybrid in {e}"
  let_expr HVector.cons _α _f as a x xs := lhs
    | throwError m!"unable to find HVector.cons in {lhs}"
  let xRealTy ← extractRiscvTy a
  let some (_, xsRealTys) := Expr.listLit? (← reduce as)
    | return .continue
  let xsRealTys ←  xsRealTys.mapM extractRiscvTy

  logInfo m!"found (llvmArgsFromHybrid (HVector.cons ({x} : {xRealTy}) ({xs} : {xsRealTys})"
  let llvmTypeType := mkApp (mkConst ``Dialect.Ty []) (mkConst ``RISCV64.RV64 [])
  let xsRealTys ← listExprToExprShallow (.some llvmTypeType) xsRealTys

  logInfo m!"calling {``riscvArgsFromHybrid_cons_eq.lemma} with {xRealTy}, {xsRealTys}, {x}, {xs}"
  logInfo m!"XXXX"
  let proof := mkAppN (mkConst ``riscvArgsFromHybrid_cons_eq.lemma []) #[xRealTy, xsRealTys, x, xs]
  logInfo m!"YYYY"
  logInfo m!"built proof {proof}"
  let proof ← reduce proof
  logInfo m!"reduced proof to {proof}"
  let eq ← reduce (← inferType proof)
  logInfo m!"reduced type of proof (i.e. the equality) to {eq}"
  let .some (_ty, _lhs, rhs) := eq.eq?
    | throwError "unable to reduce application of riscvArgsFromHybrid_cons_eq.lemma to an equality, only reduced to '{eq}'."
  logInfo m!"final right-hand-side of equality is: {rhs}"
  return .visit {
    expr := rhs,
    proof? := .some proof
  }

@[simp_denote]
theorem valuation_var_snoc_eq.lemma {Ty : Type} [TyDenote Ty] {Γ : Ctxt Ty} {t t' : Ty} {s : Γ.Valuation} {x : TyDenote.toType t} {v : Γ.Var t'} :
  (s.snoc x) (Ctxt.Var.toSnoc v) = s v := rfl


/- # ADD, riscv   -/
def add_riscv := [LV| {
    ^entry (%lhs: i64, %rhs: i64 ):
      %lhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%lhs) : (i64) -> !i64
      %rhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%rhs) : (i64) -> !i64
      %add1 = add %lhsr, %rhsr : !i64
      %addl = "builtin.unrealized_conversion_cast.riscvToLLVM" (%add1) : (!i64) -> (i64)
      llvm.return %addl : i64
  }]
/- # ADD, no flag  -/

def add_llvm_no_flags : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%lhs: i64, %rhs: i64 ):
      %1 = llvm.add   %lhs, %rhs  : i64
      llvm.return %1 : i64
  }]

/- # ADD,with  flag  -/
def add_llvm_nsw_flags : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%lhs: i64, %rhs: i64 ):
      %1 = llvm.add   %lhs, %rhs overflow<nsw>   : i64
      llvm.return %1 : i64
  }]
def add_llvm_nuw_flags : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%lhs: i64, %rhs: i64 ):
      %1 = llvm.add   %lhs, %rhs overflow<nuw>   : i64
      llvm.return %1 : i64
  }]

def add_llvm_nsw_nuw_flags : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%lhs: i64, %rhs: i64 ):
      %1 = llvm.add   %lhs, %rhs overflow<nsw,nuw>   : i64
      llvm.return %1 : i64
  }]
/- example of very manula proof ->try to extract patterns for automation-/
def llvm_add_lower_riscv_noflags : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs:= add_llvm_no_flags , rhs:= add_riscv ,
   correct := by
    unfold add_llvm_no_flags add_riscv
    set_option pp.analyze true in
    simp_peephole
    simp [builtin.unrealized_conversion_cast.riscvToLLVM,  builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_AND]
    -- intros a b
    simp [LLVM.add, RTYPE_pure64_RISCV_ADD]
    rintro (_|_) (_|_) <;> simp;
    . simp only [LLVM.add?, BitVec.Refinement.refl]
  }

def llvm_add_lower_riscv_nsw_flag : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs:= add_llvm_nsw_flags , rhs:= add_riscv ,
   correct := by
    unfold add_llvm_nsw_flags add_riscv
    set_option pp.analyze true in
    simp_peephole
    simp [builtin.unrealized_conversion_cast.riscvToLLVM,  builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_AND]
    -- intros a b
    simp [LLVM.add, RTYPE_pure64_RISCV_ADD]
    rintro (_|_) (_|_) ;
    . simp
    . simp
    . simp
    . simp
      split /- split on the overflow case: if overflow then riscv refines
      llvm by providing a default value, else they return the same value -/
      case some.some.isTrue => simp [BitVec.Refinement.none_left] -- case where llvm is poison and riscv defaults to a value
      case some.some.isFalse => simp [LLVM.add?]
  }
def llvm_add_lower_riscv_nuw_flag : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs:= add_llvm_nuw_flags , rhs:= add_riscv ,
   correct := by
    unfold add_llvm_nuw_flags add_riscv
    set_option pp.analyze true in
    simp_peephole
    simp [builtin.unrealized_conversion_cast.riscvToLLVM,  builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_AND]
    -- intros a b
    simp [LLVM.add, RTYPE_pure64_RISCV_ADD]
    rintro (_|_) (_|_) ;
    . simp
    . simp
    . simp
    . simp
      split /- split on the overflow case: if overflow then riscv refines
      llvm by providing a default value, else they return the same value -/
      case some.some.isTrue => simp [BitVec.Refinement.none_left] -- case where llvm is poison and riscv defaults to a value
      case some.some.isFalse => simp [LLVM.add?]
  }

def llvm_add_lower_riscv_nuw_nsw_flag : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs:= add_llvm_nuw_flags , rhs:= add_riscv ,
   correct := by
    unfold add_llvm_nuw_flags add_riscv
    set_option pp.analyze true in
    simp_peephole
    simp [builtin.unrealized_conversion_cast.riscvToLLVM,  builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_AND]
    -- intros a b
    simp [LLVM.add, RTYPE_pure64_RISCV_ADD]
    rintro (_|_) (_|_) ;
    . simp
    . simp
    . simp
    . simp
      split /- split on the overflow case: if overflow then riscv refines
      llvm by providing a default value, else they return the same value -/
      case some.some.isTrue => simp [BitVec.Refinement.none_left] -- case where llvm is poison and riscv defaults to a value
      case some.some.isFalse => simp [LLVM.add?]
  }

/- # AND -/
def and_llvm : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%lhs: i64, %rhs: i64 ):
      %1 = llvm.and %lhs, %rhs : i64
      llvm.return %1 : i64
      --llvm.return %lhs : i64
  }]

def and_riscv := [LV| {
    ^entry (%lhs: i64, %rhs: i64 ):
      %lhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%lhs) : (i64) -> !i64
      %rhsr = "builtin.unrealized_conversion_cast.LLVMToriscv"(%rhs) : (i64) -> !i64
       %add1 = and %lhsr, %rhsr : !i64
       %addl = "builtin.unrealized_conversion_cast.riscvToLLVM" (%add1) : (!i64) -> (i64)
      llvm.return %addl : i64
  }]


def llvm_and_lower_riscv1 : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs:= and_llvm , rhs:= and_riscv ,
   correct := by
    unfold and_llvm and_riscv
    simp_peephole
    simp [builtin.unrealized_conversion_cast.riscvToLLVM,  builtin.unrealized_conversion_cast.LLVMToriscv]
    simp [LLVM.and, RTYPE_pure64_RISCV_AND]
    rintro (_|foo) (_|bar)
    · simp
    · simp
    · simp
    · simp
      simp only [LLVM.and?, BitVec.Refinement.some_some]
      bv_decide
    }


/- # ASHR, not exact -/

def ashr_llvm_no_flag : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %1 = llvm.ashr %x, %amount : i64
      llvm.return %1 : i64
  }]

/- # ASHR,  exact -/
def ashr_llvm_exact_flag : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %1 = llvm.ashr exact %x, %amount : i64
      llvm.return %1 : i64
  }]
def ashr_riscv := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %base = "builtin.unrealized_conversion_cast.LLVMToriscv"(%x) : (i64) -> !i64
      %shamt = "builtin.unrealized_conversion_cast.LLVMToriscv"(%amount) : (i64) -> !i64
       %res = sra %base, %shamt : !i64
       %y= "builtin.unrealized_conversion_cast.riscvToLLVM" (%res) : (!i64) -> (i64)
      llvm.return %y : i64
  }]

set_option Elab.async true in
-- shifts the first arguemnt by the value of the second argument
def llvm_ashr_lower_riscv_no_flag : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := ashr_llvm_no_flag , rhs := ashr_riscv ,
    correct :=  by
      unfold ashr_llvm_no_flag ashr_riscv -- think of adding these to simp peephole
      simp_peephole
      simp_alive_undef
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|x1) (_|x2) <;> simp [RTYPE_pure64_RISCV_SRA, LLVM.ashr?]
      simp_alive_split
      case neg hf =>
                simp at hf   --this is the poison case, where llvm returns a poison value but in riscv we ouput a concret bitvec value for it,
                --have h2 :  ¬64#64 ≤ x2 = (x2 < 64#64):= by simp
                --rw [h2] at hf
                --simp [BitVec.Refinement.some_some]
                have not_leq_eq_mod  (x2 : BitVec 64) (h :x2.toNat < 64 ):  x2.toNat = x2.toNat % 64 := by
                  simp[Nat.mod_eq_of_lt h]
                -- to do : get rid of the to Nat aka do it bitwise
                sorry

     /- . simp_alive_split
        . case some.some.isTrue=> simp [BitVec.Refinement.none_left] -- this is the poison case, where llvm returns a poison value but in riscv we ouput a concret bitvec value for it,
          -- in detail riscv performs the arithemtic shift with the maximum possible shift amount
        . case some.some.isFalse =>
          simp_alive_ops
          simp [ Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, ge_iff_le,
          BitVec.sshiftRight_eq']
          split
          . case isTrue ht => simp [BitVec.Refinement]
          . case isFalse hf =>
                have h2 :  ¬64#64 ≤ x2 = (x2 < 64#64):= by simp
                rw [h2] at hf
                simp [BitVec.Refinement.some_some]
                have not_leq_eq_mod  (x2 : BitVec 64) (h :x2.toNat < 64 ):  x2.toNat = x2.toNat % 64 := by
                  simp[Nat.mod_eq_of_lt h]
                rw[← not_leq_eq_mod]
                sorry -/
  }

def llvm_ashr_lower_riscv_flag : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := ashr_llvm_exact_flag , rhs := ashr_riscv ,
    correct :=  by
      unfold ashr_llvm_exact_flag ashr_riscv -- think of adding these to simp peephole
      simp_peephole
      simp_alive_undef
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|x1) (_|x2) <;> simp [RTYPE_pure64_RISCV_SRA, LLVM.ashr?]
      simp_alive_split
      case neg hf =>
                simp at hf   --this is the poison case, where llvm returns a poison value but in riscv we ouput a concret bitvec value for it,
                --have h2 :  ¬64#64 ≤ x2 = (x2 < 64#64):= by simp
                --rw [h2] at hf
                --simp [BitVec.Refinement.some_some]
                have not_leq_eq_mod  (x2 : BitVec 64) (h :x2.toNat < 64 ):  x2.toNat = x2.toNat % 64 := by
                  simp[Nat.mod_eq_of_lt h]
                -- to do : get rid of the to Nat aka do it bitwise
                sorry

  }
-- think of to eliminate all the casts in the end --> aka cast elimination pass

/- # SRL, not exact
logical right shift operation
in LLVM: if exact flag is set, then returns poison if any non zero bit is shifted  -/

def lshr_llvm_no_flag : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %1 = llvm.lshr %x, %amount : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def srl_riscv := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %base = "builtin.unrealized_conversion_cast.LLVMToriscv"(%x) : (i64) -> !i64
      %shamt = "builtin.unrealized_conversion_cast.LLVMToriscv"(%amount) : (i64) -> !i64
       %res = srl %base, %shamt : !i64
       %y= "builtin.unrealized_conversion_cast.riscvToLLVM" (%res) : (!i64) -> (i64)
      llvm.return %y : i64
  }]

def llvm_srl_lower_riscv1 : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := lshr_llvm_no_flag , rhs := srl_riscv ,
    correct :=  by
      unfold lshr_llvm_no_flag srl_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|x1) (_|x2) <;> simp [RTYPE_pure64_RISCV_SRL,LLVM.lshr];
      . split
        . simp [BitVec.Refinement.none_left] -- this is the poison case, where llvm returns a poison value but in riscv we ouptut a concret bitvec value for it,
          -- in detail riscv performs the arithemtic shift with the maximum possible shift amount
        . simp [LLVM.lshr?]
          split
          .case some.some.isFalse.isTrue ht =>  simp [BitVec.Refinement]
            -- riscv returns the logical shift by the amount
          . case some.some.isFalse.isFalse hf =>
            simp only [BitVec.Refinement.some_some]
            have not_leq_eq_mod  (x2 : BitVec 64) (h :x2.toNat < 64 ):  x2.toNat = x2.toNat % 64 := by
              simp only [Nat.mod_eq_of_lt h]
            rw[← not_leq_eq_mod]
            have h2 :  ¬64#64 ≤ x2 = (x2 < 64#64):= by simp
            rw [h2] at hf
            have : x2 < 64#64 →  x2.toNat < 64 := by bv_omega
            apply this
            exact hf }

def lshr_llvm_exact : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %1 = llvm.lshr exact %x, %amount : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def llvm_srl_lower_riscv_exact : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := lshr_llvm_exact , rhs := srl_riscv ,
    correct :=  by
      unfold lshr_llvm_exact srl_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|x1) (_|x2) <;> simp [RTYPE_pure64_RISCV_SRL,LLVM.lshr];
      . split
        . simp [BitVec.Refinement.none_left] -- this is the poison case, where llvm returns a poison value but in riscv we ouptut a concret bitvec value for it,
          -- in detail riscv performs the arithemtic shift with the maximum possible shift amount
        . simp [LLVM.lshr?]
          split
          .case some.some.isFalse.isTrue ht =>  simp [BitVec.Refinement]
            -- riscv returns the logical shift by the amount
          . case some.some.isFalse.isFalse hf =>
            simp only [BitVec.Refinement.some_some]
            have not_leq_eq_mod  (x2 : BitVec 64) (h :x2.toNat < 64 ):  x2.toNat = x2.toNat % 64 := by
              simp only [Nat.mod_eq_of_lt h]
            rw[← not_leq_eq_mod]
            have h2 :  ¬64#64 ≤ x2 = (x2 < 64#64):= by simp
            rw [h2] at hf
            have : x2 < 64#64 →  x2.toNat < 64 := by bv_omega
            apply this
            exact hf }

/- # MUL NO FLAG

tail	__muldi3

logical right shift operation
in LLVM: if exact flag is set, then returns poison if any non zero bit is shifted  -/

/-
done in LLVM like this :
%1 = llvm.mul %x, %amount : i64 -- value depends on wether to no overflow flag is present or not
-/
def mul_llvm_noflag : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %1 = llvm.mul %x, %amount : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def mul_riscv := [LV| {
    ^entry (%r1: i64, %r2: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r1) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r2) : (i64) -> !i64
      %res = mul %x1, %x2 : !i64
      %y= "builtin.unrealized_conversion_cast.riscvToLLVM" (%res) : (!i64) -> (i64)
      llvm.return %y : i64
  }]

/- # MUL FLAGS -/

def mul_llvm_nsw : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %1 = llvm.mul %x, %amount overflow<nsw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def mul_llvm_nuw : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %1 = llvm.mul %x, %amount overflow<nuw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def mul_llvm_flags : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %1 = llvm.mul %x, %amount overflow<nsw,nuw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

/-
## Missing BitVec Lemmas.
Missing bit vector lemmas.
Are not proven yet.
-/
-- to do + evtl. mark them as simp
theorem extractLsb'_extractLsb' :
    BitVec.extractLsb' start length (BitVec.extractLsb' start' length' x)
    = (BitVec.extractLsb' (start'+start) (min length length') x).setWidth length := by
  sorry

-- to do + evtl. mark them as simp
theorem extractLsb'_extractLsb'2 {x : BitVec w} :
    BitVec.extractLsb' start length (BitVec.extractLsb' start' length' x)
    = BitVec.extractLsb' (start'+start) length (x.setWidth (start + start' + (min length length'))) := by
  -- obtain rfl : w = 16 := sorry
  -- bv_decide
  --unfold BitVec.extractLsb'
  --simp
  sorry

example {x1 x2 : BitVec 64 } : BitVec.setWidth 64 (BitVec.ofInt 129 (max (x1.toInt * x2.toInt) 0)) =
(if 0#64 > (BitVec.mul x1 x2) then 0#64 else (BitVec.mul x1 x2)) := by sorry
  -- bitwise reasoning needed -> ask for adivce

open BitVec(ofInt)
namespace BitVec
theorem Int.toNat_mod_eq {z : Int} (h : 0 ≤ z) (m : Nat) :
    z.toNat % m = (z % m).toNat := by
  cases z
  · rfl
  · contradiction

  @[simp]
  theorem setWidth_ofInt_of_le (x : Int) (w v : Nat) (h : w ≤ v) :
      setWidth w (ofInt v x) = BitVec.ofInt w x := by
      apply eq_of_toNat_eq
      simp only [toNat_setWidth, toNat_ofInt, Int.natCast_pow, Int.cast_ofNat_Int]
      rw [Int.toNat_mod_eq (by omega)]
      simp only [Int.natCast_pow, Int.cast_ofNat_Int]
      rw [Int.emod_emod_of_dvd]
      obtain ⟨k, rfl⟩ := Nat.le.dest h
      refine ⟨2 ^ k, ?_⟩
      exact Lean.Grind.CommRing.pow_add 2 w k
      -- ^^ TODO: we probably shouldn't use a Grind lemma here
end BitVec

def llvm_mul_lower_riscv_noflag : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := mul_llvm_noflag , rhs := mul_riscv ,
    correct :=  by
      unfold mul_llvm_noflag mul_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|x1) (_|x2) <;> simp ;
      . simp [LLVM.mul]
      . simp [LLVM.mul]
      . simp [LLVM.mul]
      . unfold LLVM.mul
        simp [Option.bind_eq_bind, Option.some_bind]  -- not sure if this is correctly parsed because shouldnt default flag be set to false then
        -- in this case of mul we do not care about overflow
        simp only [LLVM.mul?, MUL_pure64_ftt]
        simp [BitVec.extractLsb]
        simp [extractLsb'_extractLsb'2]
        have : 0 + min 64 128 = 64 := by omega
        rw [this]
        rw [ BitVec.extractLsb'_eq_self] -- wait until the SailLeanModell is updated to fix the semantics bug
        bv_omega
        sorry


         }
        -- to do : bitwise reasoning
        /-
        x1 * x2 =
        BitVec.extractLsb 63 0
        (BitVec.extractLsb' 0 128
        (BitVec.ofInt 129 (max (x1.toInt * x2.toInt) 0)))
        -- to do reason on a bit level -> MODULO 64 is equal to just extracting bit 63:0
        -/
      --simp [LLVM.lshr] -/


/- # MUL with  FLAG -/
/-

pseudo ops
tail	__muldi3

-/
def mul_llvm_flag : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %amount: i64 ):
      %1 = llvm.mul  %x, %amount : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]


def llvm_mul_lower_riscv1_flag : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := mul_llvm_flag , rhs := mul_riscv ,
    correct :=  by
      unfold mul_llvm_flag mul_riscv
      simp_peephole
      rintro (_|a) (_|b)<;> simp [LLVM.mul, LLVM.mul?, builtin.unrealized_conversion_cast.riscvToLLVM, builtin.unrealized_conversion_cast.LLVMToriscv ]
      . unfold MUL_pure64_ftt
        rw [ BitVec.extractLsb]
        rw [ extractLsb'_extractLsb'2]
        simp
        have : min 64 128 = 64 := by omega
        rw [this]
        simp
        sorry
       }


/- # OR non-disjoint  -/

def or_llvm_noflag : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.or  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def or_riscv := [LV| {
    ^entry (%r1: i64, %r2: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r1) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%r2) : (i64) -> !i64
      %res = or %x1, %x2 : !i64
      %y= "builtin.unrealized_conversion_cast.riscvToLLVM" (%res) : (!i64) -> (i64)
      llvm.return %y : i64
  }]

def llvm_or_lower_riscv1_noflag : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := or_llvm_noflag , rhs := or_riscv ,
    correct :=  by
      unfold or_llvm_noflag or_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|x1) (_|x2) <;> simp [RTYPE_pure64_RISCV_OR, LLVM.or];
      . split
        . case some.some.isTrue ht=> simp [BitVec.Refinement.none_left] -- this is the poison case, where llvm returns a poison value but in riscv we ouptut a concret bitvec value for it,
          -- in detail riscv performs the arithemtic shift with the maximum possible shift amount
        . case some.some.isFalse hf =>
            simp[LLVM.or?]
            bv_decide
}

/-! # OR disjoint-/

/- the disjoint flag requries that no two bits at the same index are set in either of the dialects.
This allows an or to be treated as an addition.  -/
def or_llvm_disjoint : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.or disjoint   %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def llvm_or_lower_riscv_disjoint : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := or_llvm_disjoint , rhs := or_riscv ,
    correct :=  by
      unfold or_llvm_disjoint or_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|x1) (_|x2) <;> simp [RTYPE_pure64_RISCV_OR, LLVM.or];
      . split
        . case some.some.isTrue ht=> simp [BitVec.Refinement.none_left] -- this is the poison case, where llvm returns a poison value but in riscv we ouptut a concret bitvec value for it,
          -- in detail riscv performs the arithemtic shift with the maximum possible shift amount
        . case some.some.isFalse hf =>
            simp[LLVM.or?]
            bv_decide
}

/-! # REM -/
/-
lvm into pseudoops tail	__moddi3 but only if the target cpu is not strong enough

-/
def rem_llvm : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.srem  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]
-- at the moment unsure how the conversion cast will eliminate
def rem_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%x) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%y) : (i64) -> !i64
      %1 = rem  %x1, %x2 : !i64 -- value depends on wether to no overflow flag is present or not
      %2 = "builtin.unrealized_conversion_cast.riscvToLLVM" (%1) : (!i64) -> (i64)
      llvm.return %2 : i64
  }]

-- BASICALLY AFFECTS ALL STATEMENTS
def llvm_rem_lower_riscv_disjoint : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := rem_llvm , rhs := rem_riscv,
    correct :=  by
      unfold rem_llvm rem_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      rintro (_|x1) (_|x2) <;> simp [RTYPE_pure64_RISCV_SREM, LLVM.srem, LLVM.srem?]
      . split -- poison if reminder by zero or int min reminder by -1
        . case some.some.isTrue ht=> simp [BitVec.Refinement.none_left] -- this is the poison case, where llvm returns a poison value but in riscv we ouptut a concret bitvec value for it,
          -- in detail riscv performs the arithemtic shift with the maximum possible shift amount
        . case some.some.isFalse hf =>
            simp[LLVM.srem?,REM_pure64_signed ]
            simp at hf
            cases hf
            . case intro h1 h2 =>
                split
                . case isTrue  ht =>
                    -- contradiction
                    sorry
                . case isFalse hf =>
                    sorry

              -- sorry
              --have h3 {x2 : BitVec 64}: ¬x2 = 0#64 → (x2.toInt = 0) = false := by
                --bv_omega
              --use h3
            --have h2 :

            -- sorry -- TRY TO simplify using bit vecs and not to Nat etc

}

/-! # SDIV no exact   -/
/-
tail	__divdi3
-/
def sdiv_llvm_no_exact : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sdiv  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]
-- at the moment unsure how the conversion cast will eliminate
def sdiv_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%x) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%y) : (i64) -> !i64
      --%1 = div  %x1, %x2 : !i64 -- value depends on wether to no overflow flag is present or not
      %2 = "builtin.unrealized_conversion_cast.riscvToLLVM" (%1) : (!i64) -> (i64)
      llvm.return %2 : i64
  }]

def llvm_sdiv_lower_riscv_no_flag: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := rem_llvm , rhs := rem_riscv, correct := by
    unfold rem_llvm rem_riscv
    simp_peephole
    rintro (_|a) (_|b)<;> simp only [LLVM.srem,builtin.unrealized_conversion_cast.LLVMToriscv, builtin.unrealized_conversion_cast.riscvToLLVM  ]
    . simp
    . simp
    . simp
    . simp
      simp [LLVM.srem?, REM_pure64_signed]
      sorry




     }

/-! # SDIV exact   -/

def sdiv_llvm_exact : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sdiv exact %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def llvm_sdiv_lower_riscv_exact : LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := sdiv_llvm_exact , rhs := rem_riscv, correct := by sorry }

/-! # UDIV no exact  -/
/-
tail	__udivdi3
-/

def udiv_llvm_no_exact : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.udiv  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]
-- at the moment unsure how the conversion cast will eliminate
def udiv_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%x) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%y) : (i64) -> !i64
      %1 = divu  %x1, %x2 : !i64 -- value depends on wether to no overflow flag is present or not
      %2 = "builtin.unrealized_conversion_cast.riscvToLLVM" (%1) : (!i64) -> (i64)
      llvm.return %2 : i64
  }]


def llvm_udiv_lower_riscv_no_flag: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := udiv_llvm_no_exact , rhs := udiv_riscv, correct := by
      unfold udiv_llvm_no_exact udiv_riscv
      simp_peephole
      simp [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv ]
      simp [Option.isSome]
      rintro (_|a) (_|b)
      . simp [LLVM.udiv, BitVec.Refinement,builtin.unrealized_conversion_cast.riscvToLLVM]
      . simp [LLVM.udiv, BitVec.Refinement,builtin.unrealized_conversion_cast.riscvToLLVM]
      . simp [LLVM.udiv, BitVec.Refinement,builtin.unrealized_conversion_cast.riscvToLLVM]
      . simp [LLVM.udiv, BitVec.Refinement,builtin.unrealized_conversion_cast.riscvToLLVM]
        split
        . case some.some.h_1 ht =>
            simp
        . case some.some.h_2 htt =>
          split
          · case isTrue htrue  => sorry
          · case isFalse hfalse  =>
             -- simp at hfalse
            simp [LLVM.udiv?, DIV_pure64_unsigned ]
            sorry
      }


/-! # UDIV exact   -/

def udiv_llvm_exact : Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.udiv exact  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]


def llvm_udiv_lower_riscv_flag: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := udiv_llvm_exact , rhs := udiv_riscv, correct := by
      unfold udiv_llvm_exact udiv_riscv
      simp_peephole
      rintro (_|a) (_|b)
      . simp [LLVM.udiv]
      . simp [LLVM.udiv]
      . simp [LLVM.udiv]
      . simp [LLVM.udiv]
        split
        · case some.some.isTrue ht => simp [BitVec.Refinement]
        · case some.some.isFalse hf =>
            simp [LLVM.udiv?]
            split -- case on division by zero
            · simp
            · simp [builtin.unrealized_conversion_cast.riscvToLLVM,  DIV_pure64_unsigned, builtin.unrealized_conversion_cast.LLVMToriscv ]
              sorry
               -- ask for help




       }

/-! # SHL (shift left) nsw nuw   -/

def shl_llvm_nsw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.shl  %x, %y overflow<nsw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def shl_llvm_nuw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.shl  %x, %y overflow<nuw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def shl_llvm_nsw_nuw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.shl  %x, %y overflow<nsw,nuw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

-- at the moment unsure how the conversion cast will eliminate
def shl_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%x) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%y) : (i64) -> !i64
      %1 = sll  %x1, %x2 : !i64 -- value depends on wether to no overflow flag is present or not
      %2 = "builtin.unrealized_conversion_cast.riscvToLLVM" (%1) : (!i64) -> (i64)
      llvm.return %2 : i64
  }]

def llvm_shl_lower_riscv_nsw: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := shl_llvm_nsw , rhs := shl_riscv, correct := by
        unfold shl_llvm_nsw shl_riscv
        simp_peephole
        rintro (_|a) (_|b)<;> simp [ builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv, LLVM.shl ]
        . split
          simp [LLVM.shl?, BitVec.Refinement]
          split
          . case some.some.isTrue.isTrue ht =>  simp [BitVec.Refinement]
          . case some.some.isTrue.isFalse htf =>
              simp[RTYPE_pure64_RISCV_SLL]
              have {b : BitVec 64} (h : 64#64 >b) : b.toNat  = (b.toNat % 64) := by bv_omega
              simp at htf
              apply this at htf
              rw [← htf]
          . simp [BitVec.Refinement]
         }

-- to do rest of the flags if needed


/-! # SUB, no flags   -/

def llvm_sub: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sub  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def sub_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%x) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%y) : (i64) -> !i64
      %1 = sub %x1, %x2 : !i64 -- value depends on wether to no overflow flag is present or not
      %2 = "builtin.unrealized_conversion_cast.riscvToLLVM" (%1) : (!i64) -> (i64)
      llvm.return %2 : i64
  }]

def llvm_sub_lower_riscv_no_flag: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_sub , rhs := sub_riscv, correct := by
        unfold llvm_sub sub_riscv
        simp_peephole
        rintro (_|a) (_|b)
        . simp [LLVM.sub]
        . simp [LLVM.sub]
        . simp [LLVM.sub]
        . simp [builtin.unrealized_conversion_cast.riscvToLLVM, builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_SUB]
          simp [LLVM.sub,LLVM.sub?]
      }

/-! # SUB, flags  -/

def llvm_sub_nsw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sub  %x, %y overflow<nsw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def llvm_sub_nsw_lower_riscv: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_sub_nsw , rhs := sub_riscv, correct := by
     unfold llvm_sub_nsw sub_riscv
     simp_peephole
     rintro (_|a) (_|b)
     · simp [builtin.unrealized_conversion_cast.riscvToLLVM, RTYPE_pure64_RISCV_SUB, LLVM.sub ]
     · simp [LLVM.sub ]
     · simp [LLVM.sub]
     · simp [LLVM.sub, builtin.unrealized_conversion_cast.riscvToLLVM, builtin.unrealized_conversion_cast.LLVMToriscv, LLVM.sub?, RTYPE_pure64_RISCV_SUB]
       split
       · simp [BitVec.Refinement]  -- this is the case where LLVM has a signed overflow and therefore returns a poison value.
       · simp  -- this is the case where we do not have signed overflow
  }

def llvm_sub_nuw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sub  %x, %y overflow<nuw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]
-- siubtraction with no unsigned overflow flag
def llvm_sub_nuw_lower_riscv: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_sub_nuw , rhs := sub_riscv, correct := by
    unfold llvm_sub_nuw sub_riscv
    simp_peephole
    rintro (_|a) (_|b) <;> simp only [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv, RTYPE_pure64_RISCV_SUB, LLVM.sub ]
    · simp
    · simp
    · simp
    · simp only [Bool.false_eq_true, false_and, ↓reduceIte, true_and, Option.bind_eq_bind,
      Option.some_bind, Option.getD_some, BitVec.sub_eq]
      split -- split on the unsignedOverflow given the nuw flag
      · simp
      · simp[LLVM.sub?]
    }

def llvm_sub_nsw_nuw: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.sub  %x, %y overflow<nsw, nuw> : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]
-- TO DO: automation
def llvm_sub_nsw_nuw_lower_riscv: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_sub_nsw_nuw , rhs := sub_riscv, correct := by
    unfold llvm_sub_nsw_nuw sub_riscv --unfolding
    simp_peephole -- call simp_peephole function --> need to think how much it depends on the simp_peephole implementation
    rintro (_|a) (_|b) <;> simp only [builtin.unrealized_conversion_cast.riscvToLLVM, builtin.unrealized_conversion_cast.LLVMToriscv,LLVM.sub, RTYPE_pure64_RISCV_SUB ]
    -- IDEA tag all the semantics and ops as simps
    . simp
    . simp
    . simp
    . simp
      split
      · case some.some.isTrue => -- this is the signed subtraction overflow case
          simp [BitVec.Refinement]
      · case some.some.isFalse hf =>
           simp only [Bool.not_eq_true] at hf
           split
           · simp
           · simp [LLVM.sub?]
      }

/-! # UREM I need help  -/
/-
	udiv	x8, x0, x1
	msub	x0, x8, x1, x0
-/
def llvm_urem: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.urem  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]
-- no flags needed
def urem_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%x) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%y) : (i64) -> !i64
      %1 = remu %x1, %x2 : !i64 -- value depends on wether to no overflow flag is present or not
      %2 = "builtin.unrealized_conversion_cast.riscvToLLVM" (%1) : (!i64) -> (i64)
      llvm.return %2 : i64
  }]

  def llvm_urem_lower_riscv: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_urem , rhs := urem_riscv, correct := by
    unfold llvm_urem urem_riscv
    simp_peephole
    rintro (_|a) (_|b) <;> simp only [builtin.unrealized_conversion_cast.riscvToLLVM,builtin.unrealized_conversion_cast.LLVMToriscv, BitVec.Refinement, LLVM.urem]
    . simp
    . simp
    . simp
    . simp [BitVec.Refinement , RTYPE_pure64_RISCV_XOR , builtin.unrealized_conversion_cast.riscvToLLVM, builtin.unrealized_conversion_cast.LLVMToriscv]
      simp [LLVM.urem?]
      split
      .case some.some.isTrue ht => /- Taking the remainder of a division by zero is undefined behavior -/
        simp [BitVec.Refinement]
      .case some.some.isFalse hf =>
        simp[REM_pure64_unsigned]
        split
        -- inpsect
        -- here
      bv_decide
  }
/-! # XOR   -/
def llvm_xor: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %1 = llvm.xor  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i64
  }]

def xor_riscv: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%x) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%y) : (i64) -> !i64
      %1 =  xor %x1, %x2 : !i64 -- value depends on wether to no overflow flag is present or not
      %2 = "builtin.unrealized_conversion_cast.riscvToLLVM" (%1) : (!i64) -> (i64)
      llvm.return %2 : i64
  }]

  def llvm_xor_lower_riscv: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_xor , rhs := xor_riscv, correct := by
    unfold llvm_xor xor_riscv
    simp_peephole
    rintro (_|a) (_|b) <;> simp only [LLVM.xor, LLVM.xor?, Option.bind_eq_bind, Option.some_bind]
    . simp
    . simp
    . simp
    . simp [BitVec.Refinement , RTYPE_pure64_RISCV_XOR , builtin.unrealized_conversion_cast.riscvToLLVM, builtin.unrealized_conversion_cast.LLVMToriscv]
      bv_decide
  }
/-! # XOR   -/
def llvm_icmp_ugt: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
     -- %1 = llvm.icmp_ugt  %x, %y : i64 -- value depends on wether to no overflow flag is present or not
      llvm.return %1 : i1
  }]

def riscv_icmp_ugt: Com  LLVMPlusRiscV [.llvm (.bitvec 64), .llvm (.bitvec 64)] .pure (.llvm (.bitvec 64))  := [LV| {
    ^entry (%x: i64, %y: i64 ):
      %x1 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%x) : (i64) -> !i64
      %x2 = "builtin.unrealized_conversion_cast.LLVMToriscv"(%y) : (i64) -> !i64
      %1 =  xor %x1, %x2 : !i64 -- value depends on wether to no overflow flag is present or not
      %2 = "builtin.unrealized_conversion_cast.riscvToLLVM" (%1) : (!i64) -> (i64)
      llvm.return %2 : i64
  }]

  def llvm_icmp_ugt_lower_riscv: LLVMPeepholeRewriteRefine [Ty.llvm (.bitvec 64) , Ty.llvm (.bitvec 64)] :=
  {lhs := llvm_xor , rhs := xor_riscv, correct := by
    unfold llvm_xor xor_riscv
    simp_peephole
    rintro (_|a) (_|b) <;> simp only [LLVM.xor, LLVM.xor?, Option.bind_eq_bind, Option.some_bind]
    . simp
    . simp
    . simp
    . simp [BitVec.Refinement , RTYPE_pure64_RISCV_XOR , builtin.unrealized_conversion_cast.riscvToLLVM, builtin.unrealized_conversion_cast.LLVMToriscv]
      bv_decide
  }



/- to do when can lower between widths
0000000000000000 <icmp_eq>:
       0: 00b54533     	xor	a0, a0, a1
       4: 00153513     	seqz	a0, a0
       8: 00008067     	ret

000000000000000c <icmp_ne>:
       c: 00b54533     	xor	a0, a0, a1
      10: 00a03533     	snez	a0, a0
      14: 00008067     	ret

0000000000000018 <icmp_ugt>:
      18: 00a5b533     	sltu	a0, a1, a0
      1c: 00008067     	ret

0000000000000020 <icmp_uge>:
      20: 00b53533     	sltu	a0, a0, a1
      24: 00154513     	xori	a0, a0, 0x1
      28: 00008067     	ret

000000000000002c <icmp_ult>:
      2c: 00b53533     	sltu	a0, a0, a1
      30: 00008067     	ret

0000000000000034 <icmp_ule>:
      34: 00a5b533     	sltu	a0, a1, a0
      38: 00154513     	xori	a0, a0, 0x1
      3c: 00008067     	ret

0000000000000040 <icmp_sgt>:
      40: 00a5a533     	slt	a0, a1, a0
      44: 00008067     	ret

0000000000000048 <icmp_sge>:
      48: 00b52533     	slt	a0, a0, a1
      4c: 00154513     	xori	a0, a0, 0x1
      50: 00008067     	ret

0000000000000054 <icmp_slt>:
      54: 00b52533     	slt	a0, a0, a1
      58: 00008067     	ret

000000000000005c <icmp_sle>:
      5c: 00a5a533     	slt	a0, a1, a0
      60: 00154513     	xori	a0, a0, 0x1
      64: 00008067     	ret





-/
/-- !
## Testing the application of cast "folding" pass/rewrites.
actually applying the rewrites
-/





/- this steps lowers a llvm xor instruction into a riscv xor instruction including conversion casts-/
def xor_cast_eq_xor_elim_rewrite :
  Com LLVMPlusRiscV (Ctxt.ofList [.llvm (.bitvec 64), .llvm (.bitvec 64)]) .pure (.llvm (.bitvec 64)) := rewritePeepholeAt (LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND llvm_xor_lower_riscv) 1  llvm_xor
-- if dont provide a proof it fails to apply/ display the rewrite.

def xor_extract_pure_assembly :
     Com LLVMPlusRiscV (Ctxt.ofList [.llvm (.bitvec 64), .llvm (.bitvec 64)]) .pure (.llvm (.bitvec 64)) := rewritePeepholeAt (LLVMToRiscvPeepholeRewriteRefine.toPeepholeUNSOUND llvm_xor_lower_riscv) 1  xor_cast_eq_xor_elim_rewrite
