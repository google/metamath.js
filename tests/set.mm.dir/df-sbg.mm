
axiom df-sbg
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  assert |- -g = ( g e. _V |-> ( x e. ( Base ` g ) , y e. ( Base ` g ) |-> ( x ( +g ` g ) ( ( invg ` g ) ` y ) ) ) )
end
