
axiom df-se
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  assert |- ( R Se A <-> A. x e. A { y e. A | y R x } e. _V )
end
