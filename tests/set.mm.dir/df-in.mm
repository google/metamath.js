

axiom df-in
  param vx: setvar x
  param cA: class A
  param cB: class B
  assert |- ( A i^i B ) = { x | ( x e. A /\ x e. B ) }
end
