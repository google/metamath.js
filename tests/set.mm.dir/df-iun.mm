
axiom df-iun
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assert |- U_ x e. A B = { y | E. x e. A y e. B }
end
