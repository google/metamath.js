

axiom df-dif(vx: setvar x, cA: class A, cB: class B) {

  return |- "( A \\ B ) = { x | ( x e. A /\\ -. x e. B ) }";
}
