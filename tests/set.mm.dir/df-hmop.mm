
axiom df-hmop
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  assert |- HrmOp = { t e. ( ~H ^m ~H ) | A. x e. ~H A. y e. ~H ( x .ih ( t ` y ) ) = ( ( t ` x ) .ih y ) }
end
