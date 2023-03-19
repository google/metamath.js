
axiom df-dvr
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  assert |- /r = ( r e. _V |-> ( x e. ( Base ` r ) , y e. ( Unit ` r ) |-> ( x ( .r ` r ) ( ( invr ` r ) ` y ) ) ) )
end
