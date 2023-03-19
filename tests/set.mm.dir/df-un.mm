
axiom df-un
  let vx: setvar x
  let cA: class A
  let cB: class B
  assert |- ( A u. B ) = { x | ( x e. A \/ x e. B ) }
end
