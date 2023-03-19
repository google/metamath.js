
axiom df-tx
  let vx: setvar x
  let vy: setvar y
  let vs: setvar s
  let vr: setvar r
  assert |- tX = ( r e. _V , s e. _V |-> ( topGen ` ran ( x e. r , y e. s |-> ( x X. y ) ) ) )
end
