
axiom df-plusf
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  assert |- +f = ( g e. _V |-> ( x e. ( Base ` g ) , y e. ( Base ` g ) |-> ( x ( +g ` g ) y ) ) )
end
