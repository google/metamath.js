
axiom df-oadd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- +o = ( x e. On , y e. On |-> ( rec ( ( z e. _V |-> suc z ) , x ) ` y ) )
end
