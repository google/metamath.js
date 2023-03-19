
axiom df-relexp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vn: setvar n
  let vr: setvar r
  assert |- ^r = ( r e. _V , n e. NN0 |-> if ( n = 0 , ( _I |` ( dom r u. ran r ) ) , ( seq 1 ( ( x e. _V , y e. _V |-> ( x o. r ) ) , ( z e. _V |-> r ) ) ` n ) ) )
end
