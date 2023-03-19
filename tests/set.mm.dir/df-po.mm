
axiom df-po
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assert |- ( R Po A <-> A. x e. A A. y e. A A. z e. A ( -. x R x /\ ( ( x R y /\ y R z ) -> x R z ) ) )
end
