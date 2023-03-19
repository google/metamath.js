
axiom df-bj-sngl
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assert |- sngl A = { x | E. y e. A x = { y } }
end
