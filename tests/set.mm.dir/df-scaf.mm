
axiom df-scaf
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  assert |- .sf = ( g e. _V |-> ( x e. ( Base ` ( Scalar ` g ) ) , y e. ( Base ` g ) |-> ( x ( .s ` g ) y ) ) )
end
