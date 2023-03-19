
axiom df-int
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assert |- |^| A = { x | A. y ( y e. A -> x e. y ) }
end
