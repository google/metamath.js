
axiom cmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assert class ( x e. A , y e. B |-> C )
end
