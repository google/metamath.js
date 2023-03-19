
axiom df-elwise
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vo: setvar o
  assert |- elwise = ( o e. _V |-> ( x e. _V , y e. _V |-> { z | E. u e. x E. v e. y z = ( u o v ) } ) )
end
