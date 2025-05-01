open BitVec


theorem test (a b : Bool) :
  (a || b) = (b || a) := by ac_nf -- :)


instance : Std.Commutative (fun a b : Bool => a == b) :=
  ⟨fun a b =>
  match a, b with
  | true, true   => rfl
  | true, false  => rfl
  | false, true  => rfl
  | false, false => rfl
⟩



#check  Std.Commutative


  --⟨fun a b => by decide⟩


#synth Std.Associative (· || ·) -- succeeds :)
#synth Std.Commutative (· || ·) -- succeeds :)

#synth Std.Associative (· == ·) -- fails :(
#synth Std.Commutative (· == ·) -- fails :(
