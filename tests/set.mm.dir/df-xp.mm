
axiom df-xp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assert |- ( A X. B ) = { <. x , y >. | ( x e. A /\ y e. B ) }
end
