
axiom df-lnop
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  assert |- LinOp = { t e. ( ~H ^m ~H ) | A. x e. CC A. y e. ~H A. z e. ~H ( t ` ( ( x .h y ) +h z ) ) = ( ( x .h ( t ` y ) ) +h ( t ` z ) ) }
end
