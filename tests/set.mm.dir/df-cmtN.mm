
axiom df-cmtN
  let vx: setvar x
  let vy: setvar y
  let vp: setvar p
  assert |- cm = ( p e. _V |-> { <. x , y >. | ( x e. ( Base ` p ) /\ y e. ( Base ` p ) /\ x = ( ( x ( meet ` p ) y ) ( join ` p ) ( x ( meet ` p ) ( ( oc ` p ) ` y ) ) ) ) } )
end
