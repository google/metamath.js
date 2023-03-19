

axiom df-sn
  param vx: setvar x
  param cA: class A
  assert |- { A } = { x | x = A }
end
