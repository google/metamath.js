

axiom df-if(wph: 'wff' ph, vx: 'setvar' x, cA: 'class' A, cB: 'class' B) {

  return '|-' "if ( ph , A , B ) = { x | ( ( x e. A /\\ ph ) \\/ ( x e. B /\\ -. ph ) ) }";
}
