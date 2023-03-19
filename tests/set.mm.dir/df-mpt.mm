
axiom df-mpt
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assert |- ( x e. A |-> B ) = { <. x , y >. | ( x e. A /\ y = B ) }
end
