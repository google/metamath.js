
axiom df-clel
  let vx: setvar x
  let cA: class A
  let cB: class B
  assert |- ( A e. B <-> E. x ( x = A /\ x e. B ) )
end
