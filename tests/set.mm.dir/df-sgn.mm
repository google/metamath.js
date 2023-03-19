
axiom df-sgn
  let vx: setvar x
  assert |- sgn = ( x e. RR* |-> if ( x = 0 , 0 , if ( x < 0 , -u 1 , 1 ) ) )
end
