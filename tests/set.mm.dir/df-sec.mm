
axiom df-sec
  let vx: setvar x
  let vy: setvar y
  assert |- sec = ( x e. { y e. CC | ( cos ` y ) =/= 0 } |-> ( 1 / ( cos ` x ) ) )
end
