
axiom df-dvds
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  assert |- || = { <. x , y >. | ( ( x e. ZZ /\ y e. ZZ ) /\ E. n e. ZZ ( n x. x ) = y ) }
end
