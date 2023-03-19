
axiom df-tc
  let vx: setvar x
  let vy: setvar y
  assert |- TC = ( x e. _V |-> |^| { y | ( x C_ y /\ Tr y ) } )
end
