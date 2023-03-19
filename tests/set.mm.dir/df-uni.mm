
axiom df-uni
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assert |- U. A = { x | E. y ( x e. y /\ y e. A ) }
end
