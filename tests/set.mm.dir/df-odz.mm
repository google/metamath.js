
axiom df-odz
  let vx: setvar x
  let vm: setvar m
  let vn: setvar n
  assert |- odZ = ( n e. NN |-> ( x e. { x e. ZZ | ( x gcd n ) = 1 } |-> inf ( { m e. NN | n || ( ( x ^ m ) - 1 ) } , RR , < ) ) )
end
