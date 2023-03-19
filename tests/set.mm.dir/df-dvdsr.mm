
axiom df-dvdsr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- ||r = ( w e. _V |-> { <. x , y >. | ( x e. ( Base ` w ) /\ E. z e. ( Base ` w ) ( z ( .r ` w ) x ) = y ) } )
end
