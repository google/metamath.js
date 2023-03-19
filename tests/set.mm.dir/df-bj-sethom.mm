
axiom df-bj-sethom
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assert |- -Set-> = ( x e. _V , y e. _V |-> { f | f : x --> y } )
end
