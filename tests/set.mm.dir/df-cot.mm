
axiom df-cot
  let vx: setvar x
  let vy: setvar y
  assert |- cot = ( x e. { y e. CC | ( sin ` y ) =/= 0 } |-> ( ( cos ` x ) / ( sin ` x ) ) )
end
