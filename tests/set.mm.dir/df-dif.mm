

axiom df-dif
  param vx: setvar x
  param cA: class A
  param cB: class B
  assert |- ( A \ B ) = { x | ( x e. A /\ -. x e. B ) }
end
