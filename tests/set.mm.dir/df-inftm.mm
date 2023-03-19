
axiom df-inftm
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vn: setvar n
  assert |- <<< = ( w e. _V |-> { <. x , y >. | ( ( x e. ( Base ` w ) /\ y e. ( Base ` w ) ) /\ ( ( 0g ` w ) ( lt ` w ) x /\ A. n e. NN ( n ( .g ` w ) x ) ( lt ` w ) y ) ) } )
end
