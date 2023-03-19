
axiom df-in
  let vx: setvar x
  let cA: class A
  let cB: class B
  assert |- ( A i^i B ) = { x | ( x e. A /\ x e. B ) }
end
