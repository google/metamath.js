

axiom ax-12(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {

  return '|-' "( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) )";
}
