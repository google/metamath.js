
axiom df-prt
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assert |- ( Prt A <-> A. x e. A A. y e. A ( x = y \/ ( x i^i y ) = (/) ) )
end
