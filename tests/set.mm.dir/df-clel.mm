

axiom df-clel
  param vx: setvar x
  param cA: class A
  param cB: class B
  assert |- ( A e. B <-> E. x ( x = A /\ x e. B ) )
end
