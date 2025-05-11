import SSA.Core.Framework
import SSA.Projects.DCE.DCE

-- TO DO : verfiy if the typeclass constraints I added doesnt throw an error.
variable (d : Dialect) [DialectSignature d][DecidableEq (Dialect.Ty d)] [DecidableEq (Dialect.Op d)]  [TyDenote d.Ty] [DialectDenote d] [Monad d.m] in
/- debug: section where I modified the file -/
def rewritePeephole_go_multi (fuel : ℕ) (prs : List (PeepholeRewrite d Γ t))
    (ix : ℕ) (target : Com d Γ₂ eff t₂) : Com d Γ₂ eff t₂ :=
  match fuel with
  | 0 => target
  | fuel' + 1 =>
    let target' := prs.foldl (fun acc pr => rewritePeepholeAt pr ix acc) target
    rewritePeephole_go_multi fuel' prs (ix + 1) target'

variable (d : Dialect) [DialectSignature d][DecidableEq (Dialect.Ty d)][DecidableEq (Dialect.Op d)] [TyDenote d.Ty] [DialectDenote d] [Monad d.m] in
def rewritePeephole_multi (fuel : ℕ)
   (prs : List (PeepholeRewrite d Γ t)) (target : Com d Γ₂ eff t₂) : (Com d Γ₂ eff t₂) :=
    rewritePeephole_go_multi d fuel prs 0 target
