
axiom df-dif
  let vx: setvar x
  let cA: class A
  let cB: class B
  assert |- ( A \ B ) = { x | ( x e. A /\ -. x e. B ) }
end
