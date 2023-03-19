
axiom df-fg
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  assert |- filGen = ( w e. _V , x e. ( fBas ` w ) |-> { y e. ~P w | ( x i^i ~P y ) =/= (/) } )
end
