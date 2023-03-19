
axiom df-pc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vn: setvar n
  let vr: setvar r
  let vp: setvar p
  assert |- pCnt = ( p e. Prime , r e. QQ |-> if ( r = 0 , +oo , ( iota z E. x e. ZZ E. y e. NN ( r = ( x / y ) /\ z = ( sup ( { n e. NN0 | ( p ^ n ) || x } , RR , < ) - sup ( { n e. NN0 | ( p ^ n ) || y } , RR , < ) ) ) ) ) )
end
