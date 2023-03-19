

axiom df-cleq
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  param cA: class A
  param cB: class B
  assume df-cleq.1: |- ( A. x ( x e. y <-> x e. z ) -> y = z )
  assert |- ( A = B <-> A. x ( x e. A <-> x e. B ) )
end
