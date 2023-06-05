

axiom df-in(vx: setvar x, cA: class A, cB: class B) {

  return |- "( A i^i B ) = { x | ( x e. A /\\ x e. B ) }";
}
