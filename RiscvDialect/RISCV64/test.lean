import Init.System.IO


def toInt_smod (x y : BitVec w) := x.toInt.fmod (y.toInt)


def REM_pure64_signed (rs2_val : BitVec 4) (rs1_val : BitVec 4) : BitVec 4  :=
    BitVec.extractLsb' 0 4
    (BitVec.ofInt (5) (if rs2_val.toInt = 0 then rs1_val.toInt else rs1_val.toInt.tmod rs2_val.toInt))

def REM_pure64_signed_bv (rs2_val : BitVec 4) (rs1_val : BitVec 4) : BitVec 4 :=
   rs1_val.srem rs2_val


def MUL_pure64_ftt (rs2_val : BitVec 4) (rs1_val : BitVec 4) : BitVec 4 :=
  BitVec.extractLsb 3 0 (BitVec.extractLsb' 0 8 (BitVec.ofInt 9 (rs1_val.toInt * rs2_val.toInt)))

def MUL_pure64_ftt_bv  (rs2_val : BitVec 4) (rs1_val : BitVec 4) : BitVec 4 :=
  rs2_val * rs1_val


-- needed
def MUL_pure64_tff (rs2_val : BitVec 4) (rs1_val : BitVec 4) : BitVec 4 :=
  BitVec.extractLsb 7 4 (BitVec.extractLsb' 0 8 (BitVec.ofInt 9 (rs1_val.toNat * rs2_val.toNat)))

def MUL_pure64_tff_bv  (rs2_val : BitVec 4) (rs1_val : BitVec 4) : BitVec 4 :=
   BitVec.extractLsb 7 4 (BitVec.extractLsb' 0 8 ((BitVec.zeroExtend 8 rs1_val)  * (BitVec.zeroExtend 8 rs2_val)))

def MUL_pure64_ttt (rs2_val : BitVec 4) (rs1_val : BitVec 4) : BitVec 4 :=
  BitVec.extractLsb 7 4 (BitVec.extractLsb' 0 8 (BitVec.ofInt 9 (rs1_val.toInt * rs2_val.toInt)))

-- need to first signed extend it and then compute mul and then shorten it :: to do
-- check my rewrite
def MUL_pure64_ttt_bv  (rs2_val : BitVec 4) (rs1_val : BitVec 4) : BitVec 4 :=
 BitVec.extractLsb 7 4 ((BitVec.signExtend 9 rs1_val) *  (BitVec.signExtend 9 rs2_val))

def MUL_pure64_ttf (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 (BitVec.extractLsb' 0 128 (BitVec.ofInt 129 (rs1_val.toInt * rs2_val.toNat)))

def MUL_pure64_ttf_bv (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 ((rs1_val * rs2_val))

-- ((BitVec.setWidth 32 rs1_val).toNat : Int) = (BitVec.setWidth 32 rs1_val).toInt
def REMW_pure64_unsigned (rs2_val : BitVec 4) (rs1_val : BitVec 4): BitVec 4 :=
 BitVec.signExtend 4
    (BitVec.extractLsb' 0 2
      (BitVec.ofInt 3
        (if ((BitVec.extractLsb 1 0 rs2_val).toNat : Int) = 0 then ↑(BitVec.extractLsb 1 0 rs1_val).toNat
        else ((BitVec.extractLsb 1 0 rs1_val).toNat : Int).tmod ↑(BitVec.extractLsb 1 0 rs2_val).toNat)))

def REMW_pure64_unsigned_bv (rs2_val : (BitVec 4)) (rs1_val : (BitVec 4)) : BitVec 4 :=
  BitVec.signExtend 4
      ((BitVec.extractLsb 1 0 rs1_val).umod (BitVec.extractLsb 1 0 rs2_val))

def test : IO Unit :=
  have w := 4
  for xx in [0 : 2^w] do
    for yy in [0 : 2^w] do
      have x := BitVec.ofNat 4 xx
      have y := BitVec.ofNat 4 yy
      IO.print f!"   REMW_pure64_unsigned {x.toInt}  {y.toInt} = REMW_pure64_unsigned_bv  {x.toInt}  {y.toInt}"

      if (REMW_pure64_unsigned x y)  ≠ (REMW_pure64_unsigned_bv x y) then
        IO.println f!"
        unsigned1  :  {REM_pure64_signed x  y}  {((BitVec.setWidth 2 x).toNat : Int)}
        unsigned_bv1 :  { REM_pure64_signed_bv  x  y} {  (BitVec.setWidth 2 x).toInt} "
        IO.println "FAIL"

      IO.println ""
    IO.println ""
#eval REM_pure64_signed (4#4) (-7#4) = REM_pure64_signed_bv (4#4) (-7#4)
#eval test
