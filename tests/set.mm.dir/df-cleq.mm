
axiom df-cleq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume df-cleq.1: |- ( A. x ( x e. y <-> x e. z ) -> y = z )
  assert |- ( A = B <-> A. x ( x e. A <-> x e. B ) )
end
