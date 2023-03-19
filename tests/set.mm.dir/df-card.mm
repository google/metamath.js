
axiom df-card
  let vx: setvar x
  let vy: setvar y
  assert |- card = ( x e. _V |-> |^| { y e. On | y ~~ x } )
end
