
axiom df-exid
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  assert |- ExId = { g | E. x e. dom dom g A. y e. dom dom g ( ( x g y ) = y /\ ( y g x ) = y ) }
end
