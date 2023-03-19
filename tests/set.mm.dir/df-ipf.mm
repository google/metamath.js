
axiom df-ipf
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  assert |- .if = ( g e. _V |-> ( x e. ( Base ` g ) , y e. ( Base ` g ) |-> ( x ( .i ` g ) y ) ) )
end
