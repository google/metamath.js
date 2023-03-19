
axiom df-op
  let vx: setvar x
  let cA: class A
  let cB: class B
  assert |- <. A , B >. = { x | ( A e. _V /\ B e. _V /\ x e. { { A } , { A , B } } ) }
end
