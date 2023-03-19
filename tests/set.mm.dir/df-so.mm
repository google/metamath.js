
axiom df-so
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  assert |- ( R Or A <-> ( R Po A /\ A. x e. A A. y e. A ( x R y \/ x = y \/ y R x ) ) )
end
