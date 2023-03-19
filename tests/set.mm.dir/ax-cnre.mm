
axiom ax-cnre
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assert |- ( A e. CC -> E. x e. RR E. y e. RR A = ( x + ( _i x. y ) ) )
end
