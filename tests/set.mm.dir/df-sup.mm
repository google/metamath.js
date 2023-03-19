
axiom df-sup
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  assert |- sup ( A , B , R ) = U. { x e. B | ( A. y e. A -. x R y /\ A. y e. B ( y R x -> E. z e. A y R z ) ) }
end
