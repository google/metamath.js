
axiom df-tskm
  let vx: setvar x
  let vy: setvar y
  assert |- tarskiMap = ( x e. _V |-> |^| { y e. Tarski | x e. y } )
end
