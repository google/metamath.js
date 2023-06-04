

axiom df-clel(vx: 'setvar' x, cA: 'class' A, cB: 'class' B) {

  return '|-' "( A e. B <-> E. x ( x = A /\\ x e. B ) )";
}
