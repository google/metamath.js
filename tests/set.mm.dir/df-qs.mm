
axiom df-qs
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  assert |- ( A /. R ) = { y | E. x e. A y = [ x ] R }
end
