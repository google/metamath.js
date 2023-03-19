
axiom df-comf
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vc: setvar c
  assert |- comf = ( c e. _V |-> ( x e. ( ( Base ` c ) X. ( Base ` c ) ) , y e. ( Base ` c ) |-> ( g e. ( ( 2nd ` x ) ( Hom ` c ) y ) , f e. ( ( Hom ` c ) ` x ) |-> ( g ( x ( comp ` c ) y ) f ) ) ) )
end
