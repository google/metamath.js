

axiom df-iota(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {

  return '|-' "( iota x ph ) = U. { y | { x | ph } = { y } }";
}
