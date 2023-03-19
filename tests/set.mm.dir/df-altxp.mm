
axiom df-altxp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assert |- ( A XX. B ) = { z | E. x e. A E. y e. B z = << x , y >> }
end
