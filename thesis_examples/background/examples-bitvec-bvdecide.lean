def exampleFin : Fin 64  := ⟨ 19 , by simp [Nat.reduceLT]⟩ -- Fin,
def bv32_ex1 : BitVec 32 :=  ⟨42, by simp [Nat.reducePow, Nat.reduceLT]⟩
def bv32_ex2 : BitVec 32 :=  42#32
def bv32_ex3 : BitVec 32 :=  BitVec.ofNat 32 43

#check BitVec.mul
