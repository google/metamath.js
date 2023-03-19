
axiom df-cnv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assert |- `' A = { <. x , y >. | y A x }
end
