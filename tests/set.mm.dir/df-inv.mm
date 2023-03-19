
axiom df-inv
  let vx: setvar x
  let vy: setvar y
  let vc: setvar c
  assert |- Inv = ( c e. Cat |-> ( x e. ( Base ` c ) , y e. ( Base ` c ) |-> ( ( x ( Sect ` c ) y ) i^i `' ( y ( Sect ` c ) x ) ) ) )
end
