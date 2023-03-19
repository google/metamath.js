
axiom df-sub
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- - = ( x e. CC , y e. CC |-> ( iota_ z e. CC ( y + z ) = x ) )
end
