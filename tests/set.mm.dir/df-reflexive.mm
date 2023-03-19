
axiom df-reflexive
  let vx: setvar x
  let cA: class A
  let cR: class R
  assert |- ( R Reflexive A <-> ( R C_ ( A X. A ) /\ A. x e. A x R x ) )
end
