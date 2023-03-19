
axiom df-rank
  let vx: setvar x
  let vy: setvar y
  assert |- rank = ( x e. _V |-> |^| { y e. On | x e. ( R1 ` suc y ) } )
end
