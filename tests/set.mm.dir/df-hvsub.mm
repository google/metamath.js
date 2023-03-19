
axiom df-hvsub
  let vx: setvar x
  let vy: setvar y
  assert |- -h = ( x e. ~H , y e. ~H |-> ( x +h ( -u 1 .h y ) ) )
end
