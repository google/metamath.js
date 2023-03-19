
axiom df-lnfn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  assert |- LinFn = { t e. ( CC ^m ~H ) | A. x e. CC A. y e. ~H A. z e. ~H ( t ` ( ( x .h y ) +h z ) ) = ( ( x x. ( t ` y ) ) + ( t ` z ) ) }
end
