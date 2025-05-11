import Init.System.IO

def REM_pure64_signed (rs2_val : BitVec 4) (rs1_val : BitVec 4) : BitVec 4  :=
    BitVec.extractLsb' 0 4
    (BitVec.ofInt (5) (if rs2_val.toInt = 0 then rs1_val.toInt else rs1_val.toInt.tmod rs2_val.toInt))

def REM_pure64_signed_bv (rs2_val : BitVec 4) (rs1_val : BitVec 4) : BitVec 4 :=
   rs1_val.srem rs2_val


def test : IO Unit :=
  have w := 4
  for xx in [0 : 2^w] do
    for yy in [0 : 2^w] do
      have x := BitVec.ofNat 4 xx
      have y := BitVec.ofNat 4 yy
      IO.print f!" {x.toInt} smod {y.toInt} \t:  {((REM_pure64_signed x y).toInt)} \t{((REM_pure64_signed_bv x  y).toInt)}"
      if (REM_pure64_signed x y) ≠ ( REM_pure64_signed_bv x y) then
        IO.println "\t FAIL HI"

      IO.println ""
    IO.println ""

#eval test

theorem REM_pure64_signed_REM_pure64_signed_bv (rs2_val) (rs1_val) :
  REM_pure64_signed (rs2_val) (rs1_val ) = REM_pure64_signed_bv (rs2_val) (rs1_val ) := by
    unfold REM_pure64_signed REM_pure64_signed_bv
    
