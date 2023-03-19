
axiom df-pt
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  assert |- Xt_ = ( f e. _V |-> ( topGen ` { x | E. g ( ( g Fn dom f /\ A. y e. dom f ( g ` y ) e. ( f ` y ) /\ E. z e. Fin A. y e. ( dom f \ z ) ( g ` y ) = U. ( f ` y ) ) /\ x = X_ y e. dom f ( g ` y ) ) } ) )
end
