

axiom df-sb(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {

  return '|-' "( [ y / x ] ph <-> ( ( x = y -> ph ) /\\ E. x ( x = y /\\ ph ) ) )";
}
