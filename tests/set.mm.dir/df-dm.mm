
axiom df-dm
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assert |- dom A = { x | E. y x A y }
end
