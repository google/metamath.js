
axiom ax-rrecex
  let vx: setvar x
  let cA: class A
  assert |- ( ( A e. RR /\ A =/= 0 ) -> E. x e. RR ( A x. x ) = 1 )
end
