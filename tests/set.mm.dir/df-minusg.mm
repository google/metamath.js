
axiom df-minusg
  let vx: setvar x
  let vw: setvar w
  let vg: setvar g
  assert |- invg = ( g e. _V |-> ( x e. ( Base ` g ) |-> ( iota_ w e. ( Base ` g ) ( w ( +g ` g ) x ) = ( 0g ` g ) ) ) )
end
