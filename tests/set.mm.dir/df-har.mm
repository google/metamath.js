
axiom df-har
  let vx: setvar x
  let vy: setvar y
  assert |- har = ( x e. _V |-> { y e. On | y ~<_ x } )
end
