
axiom df-ass
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vg: setvar g
  assert |- Ass = { g | A. x e. dom dom g A. y e. dom dom g A. z e. dom dom g ( ( x g y ) g z ) = ( x g ( y g z ) ) }
end
