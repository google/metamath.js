
axiom df-topgen
  let vx: setvar x
  let vy: setvar y
  assert |- topGen = ( x e. _V |-> { y | y C_ U. ( x i^i ~P y ) } )
end
