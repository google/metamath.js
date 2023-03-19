
axiom df-unop
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  assert |- UniOp = { t | ( t : ~H -onto-> ~H /\ A. x e. ~H A. y e. ~H ( ( t ` x ) .ih ( t ` y ) ) = ( x .ih y ) ) }
end
