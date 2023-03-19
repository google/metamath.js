

axiom df-op
  param vx: setvar x
  param cA: class A
  param cB: class B
  assert |- <. A , B >. = { x | ( A e. _V /\ B e. _V /\ x e. { { A } , { A , B } } ) }
end
