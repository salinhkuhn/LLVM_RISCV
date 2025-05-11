-- import RiscvDialect.RDialect
import RiscvDialect.RISCV64.all
import RiscvDialect.RefinementDialect
import SSA.Projects.InstCombine.LLVM.Semantics
import SSA.Projects.InstCombine.LLVM.PrettyEDSL
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.TacticAuto
import SSA.Projects.InstCombine.Base
import SSA.Projects.InstCombine.ForLean
import RiscvDialect.Instructions.riscv_instructions
import RiscvDialect.Instructions.llvm_instructions

import Lean

open RISCV64
open RISCVExpr
open InstCombine (LLVM)
set_option maxHeartbeats 10000000
/-
this file contains the actually implementation of the instruction selection.
we transalte a Com in operating on context of type α and dialect D1 to a com operating on context of type β and dialect D2.
-/


def LLVMCtxtToRV (Γ : Ctxt LLVM.Ty) : Ctxt RV64.Ty :=
  List.replicate Γ.length (.bv)

/--TO DO: ask for a shorter proof.-/

def LLVMVarToRV : Γ.Var (.bitvec 64) → (LLVMCtxtToRV Γ).Var .bv
  | ⟨i, h⟩ =>  ⟨i, by
    simp [LLVMCtxtToRV]
    have hcontra2 : Γ.get? i = some (InstCombine.Ty.bitvec 64) := by exact h
    have hcontra3: List.length Γ ≤ i → Γ.get? i  = none := by simp [List.get?]
    have hcontra : i <  Γ.length :=  by
      by_contra h
      simp at h
      have h_none : Γ.get? i = none := hcontra3 h
      rw [hcontra2] at h_none
      contradiction
    have leng_eq_leng : i < List.length Γ → i < List.length (List.replicate (List.length Γ) Ty.bv) := by simp
    have h3 : i < (List.replicate (List.length Γ) Ty.bv).length := by exact leng_eq_leng hcontra
    have h4 : (List.replicate (List.length Γ) Ty.bv)[i] = Ty.bv → (List.replicate (List.length Γ) Ty.bv)[i]? = some Ty.bv := by
        simp [List.get?_eq_some]
        exact hcontra
    apply h4
    rfl
   ⟩




/- - skipped so far:
LLVM MLIR copy instruction just returns a copy of the element ? -> ask what this instruction does, like why do we have it since its anyways SSA ?

-- i assume not relevant for me atm because only operate on i64 bit

trunc :: Op.trunc w w' :: truncates from w to w' bits, dont make sense in my case
zext
sext (because sign extend and zero extend doesnt make sense for this with
think how to modell it on an assembly level ,icmp and select --> compile to reiscv to see it  )
-/


-- function that rewrites ahn expression into a computation
variable {d} [DialectSignature d]
def Com.ofExpr : Expr d Γ eff t → Com d Γ eff t := fun e =>
  Com.var e <| Com.ret <| Ctxt.Var.last _ _


-- TO DO : change the semantics level of the dialect on how to get the arguments !!!!! swithc get 0 and get 1
-- in the div rem etc cases lake v

-- LLVM INSTRUCTION MAPPING TO RISCV: ONE-TO-ONE
-- this works if these are single instruction level mappings

-- how to proof this :: for all instructions th

def lowerSimpleIRInstruction  (e : Expr LLVM Γ .pure (.bitvec 64)) :  Expr  RV64 (LLVMCtxtToRV Γ) .pure (.bv)  :=
match e with
  -- CONST (which is a operation in llvm.mlir dialect but not in llvm ir), check
  | Expr.mk (InstCombine.Op.const 64 val) _ _ (.nil) _  =>
      Expr.mk (RISCV64.Op.const val) (eff_le := by constructor) (ty_eq := rfl) (.nil) .nil
  -- ADD (with or without overflow)
  | Expr.mk (InstCombine.Op.add 64 nswnuw') _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (RISCV64.Op.add) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- SUB
  | Expr.mk (InstCombine.Op.sub 64 nswnuw') _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (RISCV64.Op.sub) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil -- double check if order is correct
  -- AND
  |Expr.mk (InstCombine.Op.and 64) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (RISCV64.Op.and) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- OR NOMRAL
  |Expr.mk (InstCombine.Op.or 64  ⟨false⟩) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  => -- disjoint or aka "or":: double check the mapping
      Expr.mk (RISCV64.Op.or) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  --OR DISJOINT:: so far this case not supported by the framework , meaning if disjoint true then cannot share a bit that is one in both bit vecs.
  |Expr.mk (InstCombine.Op.or 64  ⟨true⟩) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  => -- disjoint or aka "or":: double check the mapping:: to be specified what the disjoint or will in riscv
      Expr.mk (RISCV64.Op.or) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  --XOR
  |Expr.mk (InstCombine.Op.xor 64 ) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (RISCV64.Op.xor) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
   --SHL (no matter the flags the riscv ersion is a refinement as one overflow it hardcodes the value to -1 while llvm would emit a poison value )
  -- the riscv is a refinement because it extract the lower 6 bits any wont ever reach the overflow case, so while llvm has a poison value, rsicv choose the value in an elegant way.
  |Expr.mk (InstCombine.Op.shl 64 flags ) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (RISCV64.Op.sll) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- logical shift right ----debug:riscv first value is shift amount !!! error prone when modelling
  |Expr.mk (InstCombine.Op.lshr 64 flags ) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (RISCV64.Op.srl) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- arithmetic shift right, --debug: riscv first value is shift amount !!! error prone when modelling
  | Expr.mk (InstCombine.Op.ashr 64 flags ) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (RISCV64.Op.sra) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  --MUL
  |Expr.mk (InstCombine.Op.mul 64 ⟨false, false⟩ ) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (RISCV64.Op.mul) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- SDIV -- the exact flags requires exact division, requires the reminder to be zero else will return poison value, riscv here is a refinement because will still execute it
  |Expr.mk (InstCombine.Op.sdiv 64 flags ) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  => -- llvm e1/e2 while riscv takes the divisor first
      Expr.mk (RISCV64.Op.div) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- UDIV
  |Expr.mk (InstCombine.Op.udiv 64 flags ) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  => -- llvm e1/e2, order in riscv is reverse
      Expr.mk (RISCV64.Op.divu) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
   --UREM ::  unsigned reminder (again here riscv a refinement because it returns first arg while llvm would return poison on mod 0)
  |Expr.mk (InstCombine.Op.urem 64 ) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  =>
      Expr.mk (RISCV64.Op.remu) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  --SREM :: signed reminder, riscv is refinement because llvm returns 0 is mod 0 but riscv returns first argument
  | Expr.mk (InstCombine.Op.srem 64 ) _ _ (e1 ::ₕ (e2 ::ₕ .nil)) _  => -- llvm: x smod y
      Expr.mk (RISCV64.Op.rem) (eff_le := by constructor) (ty_eq := rfl) (.cons  (LLVMVarToRV e1)  <| .cons (LLVMVarToRV e2)  <| .nil) .nil
  -- FALLBACK FUNCTION
  |e => Expr.mk (RISCV64.Op.const 0) (eff_le := by constructor) (ty_eq := rfl) (.nil) (.nil)
-- !!!!!! check operator order in llvm vs riscv not modelled the same espeically for div and rem etc.


/- this function describes how to create a valuation for the riscv context given a valuation for the llvm contex.
Since our mapping is is one to one, we map the index one to one because it is constructed that way during the lowering process.
If the LLVM context contains a none, we map it to zero in the LLVM context.
 -/

/-
this creates a RISC-V valuation given a LLVM valuation. Valuation is a function that takes in a type t and a variable
and returns an element that has the corresponding type and is specified by the valuation.
-/
open InstCombine (Ty) in
def LLVMValuationToRV {Γ : Ctxt LLVM.Ty} (V : Γ.Valuation) : (LLVMCtxtToRV Γ).Valuation :=
  fun t v => -- A valuation is a function that takes in a type and variable (index and proof that it has the correspondig type) and returns an value of the correct type.
    match t with
    | .bv =>
      let i : Fin Γ.length := ⟨v.1, by -- extract information from the llvm variable
          simpa [LLVMCtxtToRV, List.getElem?_eq_some_iff ] using v.prop
       ⟩ -- this is a simplification for simp [...] at using h where we defined h to be v.prop
      match h : Γ.get i with -- trick to get a let binding into the list of things we know.
      | Ty.bitvec w =>
           let (v' : Γ.Var (Ty.bitvec w)) := ⟨v.1, by
              simpa [List.getElem?_eq_some_iff,i, i.prop] using h
        ⟩
        (V v' : LLVM.IntW w).getD 0#_ |>.setWidth 64 -- return the underlying val where some val else hard code poison values to zero.
-- here with extract the value of the llvm variable and if the value is a none with convert it to zero bitvector.We then set the width to 64 bits.

/-
other version of the proof
      match h : Γ.get i with
      | Ty.bitvec w =>
        let (v' : Γ.Var (Ty.bitvec w)) := ⟨v.1, by
            have h_lt : v.1 < _ := i.prop
            simpa [List.getElem?_eq_some_iff, h_lt] using h
            ⟩
        (V v' : LLVM.IntW w).getD 0#_ |>.setWidth 64 -- return the underlying val where some val else hard code poison values to zero.



-/

/-want to prove that for all InstCombine.Op for which isOneToOne (op) == true, we have that
lowerSimpleIRInstruction_correct

extend the statement to: ∀ e,  (isOneToOne e) → ∀ x, (e.denote V) = some x → (lowerSimpleIRInstruction e).denote (LLVMValuationToRV V) = x

 -/
-- or might proof statement where assume denotation is monton regarding valutation -> harder
theorem lowerSimpleIRInstruction_correct
    (e : Expr LLVM Γ .pure (.bitvec 64)) (V : Γ.Valuation) :
    ∀ x, (e.denote V) = some x → (lowerSimpleIRInstruction e).denote (LLVMValuationToRV V) = x := by
  intros x h1
  rcases e with ⟨op1, ty_eq1, eff_le1,args1, regionArgs1⟩
  case mk =>
    cases op1
    case unary w op =>
      cases op
      /- case neg => sorry
      case not => sorry
      case copy => sorry
      case trunc => sorry
      case zext => sorry
      case sext => sorry-/
    case binary w op =>
      cases op
      .
        simp at ty_eq1
        unfold DialectSignature.outTy at ty_eq1
        simp at ty_eq1
        simp [signature] at ty_eq1
        subst ty_eq1
        simp [lowerSimpleIRInstruction]
        unfold DialectSignature.sig at args1
        simp at args1
        simp only [signature, InstCombine.MOp.sig,InstCombine.MOp.outTy] at args1
        unfold DialectSignature.effectKind at eff_le1
        simp at eff_le1
        simp only [signature] at eff_le1
        -- simp_peephole at h1 when apply these the whole hyptohesis h vanishes
        simp_peephole
        





    /-
      case or => sorry
      case xor => sorry
      case shl => sorry
      case lshr => sorry
      case ashr => sorry
      case urem => sorry
      case srem => sorry
      case add => sorry
      case mul => sorry
      case sub => sorry
      case sdiv => sorry
      case udiv => sorry
    case select => sorry
    case icmp => sorry
    case const => sorry
-/
#check Ctxt.Hom

#check Ctxt.snoc
#check Ctxt.Hom.snocMap

-- Γ ++ Δ = Γ.snoc Δ₀ |>.snoc Δ₁ ...
#check Ctxt.Var

/- -TO DO: implement prepending of one computation onto antoher computation
this function preprends a computation onto another computation => to do : think of how to do this -/
/-
preprends a computation e to a computation body.
the computation body must then still be well typed under the context where we have the let bindings introduced by the com e.
-/
variable {d : Dialect} [DialectSignature d] in
def Com.prependCom (e : Com d Γ eff α) (body : Com d (Γ.snoc α) eff β) : Com d Γ eff β :=
  go .id e
where
  go {Δ} (f : Γ.Hom Δ) : Com d Δ eff α → Com d Δ eff β -- the homomorphism the mapping from how the variables in Γ are to be found in Δ
    | Com.var e' body' => Com.var e' (go (f.snocRight) body')
    | Com.ret returnVar =>
        -- Δ = Γ ++ ...
        body.changeVars fun t v =>
          by
            cases v
            next v => exact f v
            next v  => exact returnVar

#check Com.var
#check Com.changeVars

/-
variable {d : Dialect} [DialectSignature d] in
def Com.prependCom2 (e : Com d Γ eff α) (body : Com d (Γ.snoc α) eff β) : Com d Γ eff β :=
  /-
  check its size , extend the context-/
  let diff :=  e.size -- this will be the diffrence in the context between init and out -> gives us how many let bindings need to be traverrsed
  -- need to shift all the variables at the point where e then is executed by certain amount
  let eOutContext := e.outContext
  go e
  where
  go : Com d _ eff α → Com d _ eff β
  | Com.var expr (Com.ret _) => Com.var expr (body) -- also not sure if the context is to long here now
  | Com.var expr (nonret) => Com.var expr (go nonret)
  |_ => sorry
-/
/- the still need to shift the indicies -/
  /-
    travers the com until the return statement, replace the return statement with the body ?
 -/




/-
need to find the return statement and insert there
then need to move the indexes of all the variables that will be added to the context afterwards by size of the computation of e
-/

/--- LLVM INSTRUCTIONS THAT MAP TO MANY RISCV INSTRUCTION
-- the purpose of this function is account for one to many lowerings where to mapping is not trivial. -/
def lowerDecomposableIR  : (e : Expr LLVM Γ .pure (.bitvec 64)) →  Com RV64 (LLVMCtxtToRV Γ) .pure (.bv)
  -- neg = const 0 && sub
  | Expr.mk (InstCombine.Op.neg 64) _ _ ((e1 ::ₕ .nil)) _ =>
        let expr1 := Expr.mk (RISCV64.Op.const (0)) (eff_le := by constructor) (ty_eq := rfl) (.nil) (.nil);
        let expr2 := Expr.mk (RISCV64.Op.sub) (eff_le := by constructor) (ty_eq := rfl) ( (LLVMVarToRV (Ctxt.Var.last _ _)) ::ₕ ((LLVMVarToRV e1) ::ₕ .nil)) .nil
        --  Com.prependCom (Com.ofExpr expr1) (Com.ofExpr expr2)
        Com.var expr1 (Com.var (expr2)  (Com.ret (Ctxt.Var.last _ _)))
  --NOT implemented as const (-1) and then xor
  | Expr.mk (InstCombine.Op.not 64) _ _ ((e1 ::ₕ .nil)) _ =>
        let expr1 := Expr.mk (RISCV64.Op.const (-1)) (eff_le := by constructor) (ty_eq := rfl) (.nil) (.nil);
        let expr2 := Expr.mk (RISCV64.Op.xor) (eff_le := by constructor) (ty_eq := rfl) ( (LLVMVarToRV (Ctxt.Var.last _ _)) ::ₕ ((LLVMVarToRV e1) ::ₕ .nil)) .nil
        --  Com.prependCom (Com.ofExpr expr1) (Com.ofExpr expr2)
        Com.var expr1 (Com.var (expr2)  (Com.ret (Ctxt.Var.last _ _)))
    --COPY:: was given in the llvm dialect but not sure why we have it
  | Expr.mk (InstCombine.Op.copy 64) _ _ (.cons e1 <| .nil) _  => -- basically returns the identity again
        let expr1 := Expr.mk (RISCV64.Op.const (0)) (eff_le := by constructor) (ty_eq := rfl) (.nil) (.nil);
        let expr2 := Expr.mk (RISCV64.Op.or) (eff_le := by constructor) (ty_eq := rfl) ( (LLVMVarToRV (Ctxt.Var.last _ _)) ::ₕ ((LLVMVarToRV e1) ::ₕ .nil)) .nil
        Com.var expr1 (Com.var (expr2) (Com.ret (Ctxt.Var.last _ _)))
  | e => Com.ofExpr (lowerSimpleIRInstruction e) -- fall back case of when this function actually gets called with a expr that can be mapped one to one


-- TO DO: unsure if like this modelling as an option, makes things not that pretty.
-- THIS FUNCTION ONLY SUPPORTS ONE TO ONE LOWERINGS
-- if we return a none then we must have an invalid input or the computation must have failed,
/-def loweringLLVMtoRISCV : {Γ : Ctxt LLVM.Ty} → (com : Com LLVM Γ .pure (.bitvec 64)) → Option (Com RV64 (LLVMCtxtToRV Γ)  .pure (.bv))
  | _, Com.ret x  =>  some (Com.ret (LLVMVarToRV x))
  | _, Com.var (α := InstCombine.Ty.bitvec 64) e c' =>
        let e' := (lowerSimpleIRInstruction e) -- map the expression to a riscv expression
        match loweringLLVMtoRISCV c' with
        | some com => some (Com.var (e') (com))
        | none => none
  | _, Com.var (α := InstCombine.Ty.bitvec _) _ _ =>
      none
-/
def isOneToOne (expr : Expr LLVM Γ .pure (.bitvec 64)) :=
  match expr.op  with
  | InstCombine.Op.neg 64 | InstCombine.Op.not 64 | InstCombine.Op.copy 64  => false
  |_ => true

/-
this function computes the LLVM to RISCV lowering, return some comp, where comp is the corresponding riscv lowering.
Returning none if the type of operation is not on a bitvec 64.
Which is not expected and supported as register and llvm ir operations are definedc on 64-bit vectors.
-/

-- this function supports onetoone and onetomany lowerings
def loweringLLVMtoRISCVextended : {Γ : Ctxt LLVM.Ty} → (com : Com LLVM Γ .pure (.bitvec 64)) → Option (Com RV64 (LLVMCtxtToRV Γ)  .pure (.bv))
  | _, Com.ret x  =>  some (Com.ret (LLVMVarToRV x))
  | _, Com.var (α := InstCombine.Ty.bitvec 64) e c' =>
        if (isOneToOne e) then
          let e' := (lowerSimpleIRInstruction e) -- map the expression to a riscv expression
          match loweringLLVMtoRISCVextended c' with
          | some com => some (Com.var (e') (com))
          | none => none
        else -- the one to many case
          let comp :=  lowerDecomposableIR e -- the computation that is needed to represent the lowering of the llvm instruction
          match loweringLLVMtoRISCVextended c' with
          | some com => some (Com.prependCom comp com ) -- this  preprends the computation needed for the expression lowering to the rest of the computation.
          | none => none
  | _, Com.var (α := InstCombine.Ty.bitvec _) _ _ =>
      none

-- bellow are examples to check my lowerings
def llvm_const :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.mlir.constant(0) :i64
      llvm.return %v1 : i64
  }]

def riscv_const := -- pretty printed version
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = const (0) : !i64
    ret %v1 : !i64
  }]


def llvm_ashr :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.ashr  %Y, %X : i64
      llvm.return %v1 : i64
  }]

def riscv_sra :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = sra %Y, %X  : !i64
          ret %v1 : !i64
  }]



def llvm_lshr :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.lshr  %Y, %X : i64
      llvm.return %v1 : i64
  }]

def riscv_slr :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = srl %Y, %X : !i64
          ret %v1 : !i64
  }]

def llvm_shl :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.shl  %Y, %X : i64
      llvm.return %v1 : i64
  }]

def riscv_sll :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = sll %Y, %X : !i64
    ret  %v1 : !i64
  }]


def llvm_urem :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.urem  %Y, %X : i64
      llvm.return %v1 : i64
  }]

def riscv_urem :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = remu %Y, %X  : !i64
    ret %v1 : !i64
  }]


def llvm_srem :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.srem  %Y, %X : i64
      llvm.return %v1 : i64
  }]

def riscv_srem :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = rem %Y, %X : !i64
    ret %v1 : !i64
  }]

def llvm_udiv :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.udiv  %Y, %X : i64
      llvm.return %v1 : i64
  }]

def riscv_udiv :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = divu %Y, %X : !i64
    ret  %v1 : !i64
  }]

def llvm_sdiv :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.sdiv  %Y, %X : i64
      llvm.return %v1 : i64
  }]

def riscv_sdiv :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "div" (%Y, %X ) : (!i64, !i64) -> (!i64)
    "ret" (%v1) : (!i64, !i64) -> ()
  }]

def llvm_sub1 :=
    [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.sub  %Y, %X : i64
      llvm.return %v1 : i64
  }]

def riscv_sub1 :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "sub" (%Y, %X ) : (!i64, !i64) -> (!i64)
    "ret" (%v1) : (!i64, !i64) -> ()
  }]

def riscv_add_add :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "add" (%X, %Y) : (!i64, !i64) -> (!i64)
    "ret" (%v1) : (!i64, !i64) -> ()
  }]

def llvm_add_add :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add  %X, %Y : i64
      llvm.return %v1 : i64
  }]

def riscv_add_sub :=
  [RV64_com| {
    ^entry (%X: !i64, %Y: !i64):
    %v1 = "add" (%X, %Y) : (!i64, !i64) -> (!i64)
    %v2 = "sub" (%v1, %v1) : (!i64, !i64) -> (!i64)
    "ret" (%v2) : (!i64, !i64) -> ()
  }]

def llvm_add_sub :=
  [llvm(64)| {
^bb0(%X : i64, %Y : i64):
      %v1 = llvm.add  %X, %Y : i64
      %v2 = llvm.sub %v1, %v1 : i64
      llvm.return %v2 : i64
  }]
#eval  loweringLLVMtoRISCVextended llvm_add_sub

def llvm_const_add :=
    [llvm(64)| {
^bb0(%X : i64):
      %v1 = llvm.mlir.constant 0 :i64
      %v2 = llvm.add  %X, %v1 : i64
      llvm.return %v2 : i64
  }]

def llvm_neg :=
    [llvm(64)| {
      ^bb0(%X : i64):
      %v1 = llvm.neg %X :i64
      llvm.return %v1 : i64
  }]
#eval loweringLLVMtoRISCVextended llvm_neg
def riscv_neg :=
  [RV64_com| {
    ^entry (%X: !i64):
    %v1 = "const" () { val = 0 : !i64 } : (!i64, !i64) -> (!i64)
    %v2 = "sub" (%v1, %X) : (!i64, !i64) -> (!i64)
    "ret" (%v2) : (!i64, !i64) -> ()
  }]

def llvm_not :=
    [llvm(64)| {
      ^bb0(%X : i64):
      %v1 = llvm.not %X :i64
      llvm.return %v1 : i64
  }]

def riscv_not :=
  [RV64_com| {
    ^entry (%X: !i64):
    %v1 = "const" () { val = -1 : !i64 } : (!i64, !i64) -> (!i64)
    %v2 = "xor" ( %v1, %X) : (!i64, !i64) -> (!i64)
    "ret" (%v2) : (!i64, !i64) -> ()
  }]

def riscv_const_add :=
  [RV64_com| {
    ^entry (%X: !i64):
    %v1 = "const" () { val = 0 : !i64 } : (!i64, !i64) -> (!i64)
    %v2 = "add" (%X, %v1) : (!i64, !i64) -> (!i64)
    "ret" (%v2) : (!i64, !i64) -> ()
  }]

  def llvm_const_add_neg_add :=
      [llvm(64)| {
      ^bb0(%X : i64):
      %v1 = llvm.mlir.constant 123848392 :i64
      %v2 = llvm.add %X, %v1 :i64
      %v3 = llvm.neg %X :i64
      %v4 = llvm.add %v2, %v1 :i64
      llvm.return %v4 : i64
  }]

  def riscv_const_add_neg_add :=
      [RV64_com| {
      ^bb0(%X : !i64):
      %v1 = "const " () { val = 123848392 : !i64 } : (!i64, !i64) -> (!i64)
      %v2 = "add" (%X, %v1) : (!i64, !i64) -> (!i64)
      %v3 = ".const " () { val = 0 : !i64 } : (!i64, !i64) -> (!i64)
      %v4 = "sub" (%v3, %X) : (!i64, !i64) -> (!i64)
      %v = "add" (%v2, %v1) : (!i64, !i64) -> (!i64)
      "ret" (%v) : (!i64, !i64) -> ()
  }]

  def llvm_only_many :=
      [llvm(64)| {
      ^bb0(%X : i64, %Y : i64):
      %v3 = llvm.neg %X :i64
      %v4 = llvm.not %Y :i64
      %v5 = llvm.not %X :i64
      llvm.return %v4 : i64
  }]

  def riscv_only_many :=
      [RV64_com| {
      ^bb0(%reg1 : !i64, %reg2 : !i64):
      %v1 = const (0) : !i64
      %v2 = sub %v1, %reg1 : !i64
      %v3 = "const " () { val = -1 : !i64 } : (!i64, !i64) -> (!i64)
      %v4 = xor  %v3, %reg2 : !i64
      %v5 = "const " () { val = -1 : !i64 } : (!i64, !i64) -> (!i64)
      %v6 = xor %v5, %reg1  : !i64
      ret %v4: !i64
  }]



def loweringMixedExample : loweringLLVMtoRISCVextended llvm_const_add_neg_add = some (riscv_const_add_neg_add):= by native_decide

def loweringOnlyManyExample : loweringLLVMtoRISCVextended llvm_only_many = some (riscv_only_many):= by native_decide

-- TEST LOWERINGS FOR THE ONE TO ONE LOWERING
--def loweringLLVMNegAsExpected :  loweringLLVMtoRISCV (llvm_neg) = some (riscv_neg) := by native_decide :: not supported because requires many to many lowering
-- checking that the lowering yield code as expected
def loweringLLVMAddAsExpected : loweringLLVMtoRISCVextended llvm_add = some (riscv_add) := by native_decide
def loweringLLVMSubExpected : loweringLLVMtoRISCVextended llvm_sub1 = some (riscv_sub1) := by native_decide
def loweringLLVMDoubleAddAsExpected : loweringLLVMtoRISCVextended llvm_add_add = some (riscv_add_add) := by native_decide
def loweringLLVMAddSubAsExpected :loweringLLVMtoRISCVextended llvm_add_sub = some (riscv_add_sub) := by native_decide
def loweringConstAdd : loweringLLVMtoRISCVextended llvm_const_add = some (riscv_const_add) := by native_decide
def loweringLLVMSDivAsExpected : loweringLLVMtoRISCVextended llvm_sdiv = some (riscv_sdiv) := by native_decide
def loweringLLVMUDivAsExpected : loweringLLVMtoRISCVextended llvm_udiv = some (riscv_udiv) := by native_decide
def loweringLLVMSRemAsExpected : loweringLLVMtoRISCVextended llvm_srem = some (riscv_srem) := by native_decide
def loweringLLVMSUemAsExpected : loweringLLVMtoRISCVextended llvm_urem = some (riscv_urem) := by native_decide

def loweringLLVMAsExpected : loweringLLVMtoRISCVextended  llvm_not = some (riscv_not) := by native_decide

def loweringLLVMShlAsExpected : loweringLLVMtoRISCVextended llvm_shl = some (riscv_sll) := by native_decide
def loweringLLVMSraAsExpected : loweringLLVMtoRISCVextended llvm_ashr = some (riscv_sra) := by native_decide
def loweringLLVMSlrAsExpected : loweringLLVMtoRISCVextended llvm_lshr = some (riscv_slr) := by native_decide
def loweringLLVMConstAsExpected : loweringLLVMtoRISCVextended (llvm_const) = some (riscv_const) := by native_decide





def rhs_add0_com :  Com RV64 [.bv] .pure .bv := Com.ret ⟨0, by simp [Ctxt.snoc]⟩
#check rhs_add0_com



-- TEST LOWERINGS FOR THE ONE TO MANY LOWERING : CANT EVALUATE YET BECAUSE LEMMA NOT PROVEN AT THE MOMENT
def loweringLLVMNegAsExpected2 :  loweringLLVMtoRISCVextended (llvm_neg) = some (riscv_neg) := by native_decide
-- examples and checks wether this is lowering makes sense
def rhs_add0_com2 :  Com RV64 [.bv] .pure .bv := Com.ret ⟨0, by simp [Ctxt.snoc]⟩
#check rhs_add0_com
-- checking that the lowering yield code as expected
def loweringLLVMAddAsExpected2 : loweringLLVMtoRISCVextended llvm_add = some (riscv_add) := by native_decide
-- because sub lowering doesnt exist yet
def loweringLLVMSubExpected2 : loweringLLVMtoRISCVextended llvm_sub1 = some (riscv_sub1) := by native_decide
def loweringLLVMDoubleAddAsExpected2 : loweringLLVMtoRISCVextended llvm_add_add = some (riscv_add_add) := by native_decide
def loweringLLVMAddSubAsExpected2 : loweringLLVMtoRISCVextended llvm_add_sub = some (riscv_add_sub) := by native_decide
def loweringConstAdd2 : loweringLLVMtoRISCVextended llvm_const_add = some (riscv_const_add) := by native_decide

def rhs : Com RV64 [.bv] .pure .bv := Com.var (RISCVExpr.const 0) (
  Com.var (RISCVExpr.add ⟨1, by simp[Ctxt.snoc]⟩ ⟨0, by simp[Ctxt.snoc]⟩) -- x + 0
      (Com.ret ⟨2, by simp[Ctxt.snoc]⟩))


-- now just need to revert this and rewrite it into the IR again


--PLAYING AROUND WITH PEEPLHOLE OPTIMIZATIONS
-- couldnt figue out to appy the rewrites onto a some Computation yet.
--def optimizedCode: Com RV64 [.bv] .pure .bv := rewritePeepholeAt rewrite_add0 1 riscv_const_add
-- now try run rewritting pass on the generated riscv-code
--def applyPeepholeOptimizationOnRewritten : some (optimizedCode) = some rhs := by native_decide

/-
def loweringLLVMRet :  loweringLLVMtoRISCV llvm_ret = some (riscv_ret) := by native_decide
def loweringLLVMReturnAsExpected :
  some  ([RV64_com| {
    ^entry (%0 : !i64 ):
      "return" (%0) : ( !i64 ) -> ()
  }])
  =
  (loweringLLVMtoRISCV (
  [llvm(64)| {
    ^bb0(%X : i64):
    llvm.return %X : i64
  }])) := by native_decide
-/
