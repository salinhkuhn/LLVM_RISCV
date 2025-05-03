
 

define i64 @gin(i64 %x) {
entry:
  ; Initial constants
  %k1 = add i64 %x, %x
  %k2 = xor i64 %k1, %x
  %k3 = mul i64 %k2,  %k2
  %k4 = or i64 %k3, %k1
  %k5 = sub i64 %k4, %k2
  ; First transformation round
  %r1 = xor i64 %k5, %x
  %r2 = add i64 %r1, %k1
  %r3 = mul i64 %r2, 31
  %r4 = or i64 %r3, %k2
  %r5 = sub i64 %r4, %r1

  ret i64 %r5
}

 define i64 @main(i64 %x)  {
  %2 = call i64 @gin(i64 %x)
  %3 = add nsw i64 %2, %x
  ret i64 %3
}
