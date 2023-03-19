
axiom df-join
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vp: setvar p
  assert |- join = ( p e. _V |-> { <. <. x , y >. , z >. | { x , y } ( lub ` p ) z } )
end
