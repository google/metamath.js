

axiom df-cleq(vx: setvar x, vy: setvar y, vz: setvar z, cA: class A, cB: class B) {
  assume df-cleq.1: |- "( A. x ( x e. y <-> x e. z ) -> y = z )";

  return |- "( A = B <-> A. x ( x e. A <-> x e. B ) )";
}
