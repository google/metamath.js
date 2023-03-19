
axiom df-div
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- / = ( x e. CC , y e. ( CC \ { 0 } ) |-> ( iota_ z e. CC ( y x. z ) = x ) )
end
