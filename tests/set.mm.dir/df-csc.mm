
axiom df-csc
  let vx: setvar x
  let vy: setvar y
  assert |- csc = ( x e. { y e. CC | ( sin ` y ) =/= 0 } |-> ( 1 / ( sin ` x ) ) )
end
