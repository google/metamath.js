
axiom df-map
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assert |- ^m = ( x e. _V , y e. _V |-> { f | f : y --> x } )
end
