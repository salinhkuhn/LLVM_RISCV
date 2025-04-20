/--

(ty_eq : ty = DialectSignature.outTy op)
to proof this we can either pass `rfl`object or a proof `by rfl`
This is the diffrence between term and tactic mode.
Either directly provide an element of the type or advise Lean in `tactic mode`
how to construct the corresponding term

-/
