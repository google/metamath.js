

axiom df-fv
  param vx: setvar x
  param cA: class A
  param cF: class F
  assert |- ( F ` A ) = ( iota x A F x )
end
