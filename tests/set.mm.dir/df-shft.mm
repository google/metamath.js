
axiom df-shft
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  assert |- shift = ( f e. _V , x e. CC |-> { <. y , z >. | ( y e. CC /\ ( y - x ) f z ) } )
end
