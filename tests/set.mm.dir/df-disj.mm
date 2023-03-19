
axiom df-disj
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assert |- ( Disj_ x e. A B <-> A. y E* x e. A y e. B )
end
