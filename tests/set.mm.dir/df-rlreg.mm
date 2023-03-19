
axiom df-rlreg
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  assert |- RLReg = ( r e. _V |-> { x e. ( Base ` r ) | A. y e. ( Base ` r ) ( ( x ( .r ` r ) y ) = ( 0g ` r ) -> y = ( 0g ` r ) ) } )
end
