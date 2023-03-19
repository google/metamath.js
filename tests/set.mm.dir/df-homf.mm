
axiom df-homf
  let vx: setvar x
  let vy: setvar y
  let vc: setvar c
  assert |- Homf = ( c e. _V |-> ( x e. ( Base ` c ) , y e. ( Base ` c ) |-> ( x ( Hom ` c ) y ) ) )
end
