

axiom df-op(vx: 'setvar' x, cA: 'class' A, cB: 'class' B) {

  return '|-' "<. A , B >. = { x | ( A e. _V /\\ B e. _V /\\ x e. { { A } , { A , B } } ) }";
}
