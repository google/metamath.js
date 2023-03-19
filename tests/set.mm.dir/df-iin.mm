
axiom df-iin
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assert |- |^|_ x e. A B = { y | A. x e. A y e. B }
end
