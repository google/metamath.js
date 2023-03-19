
axiom df-adjh
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vt: setvar t
  assert |- adjh = { <. t , u >. | ( t : ~H --> ~H /\ u : ~H --> ~H /\ A. x e. ~H A. y e. ~H ( ( t ` x ) .ih y ) = ( x .ih ( u ` y ) ) ) }
end
