

axiom ax-cnre
  param vx: setvar x
  param vy: setvar y
  param cA: class A
  assert |- ( A e. CC -> E. x e. RR E. y e. RR A = ( x + ( _i x. y ) ) )
end
