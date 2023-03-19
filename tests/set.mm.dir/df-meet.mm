
axiom df-meet
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vp: setvar p
  assert |- meet = ( p e. _V |-> { <. <. x , y >. , z >. | { x , y } ( glb ` p ) z } )
end
