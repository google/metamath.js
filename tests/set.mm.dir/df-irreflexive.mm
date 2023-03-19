
axiom df-irreflexive
  let vx: setvar x
  let cA: class A
  let cR: class R
  assert |- ( R Irreflexive A <-> ( R C_ ( A X. A ) /\ A. x e. A -. x R x ) )
end
