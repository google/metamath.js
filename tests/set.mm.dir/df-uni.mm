

axiom df-uni
  param vx: setvar x
  param vy: setvar y
  param cA: class A
  assert |- U. A = { x | E. y ( x e. y /\ y e. A ) }
end
