

axiom df-clab(wph: 'wff' ph, vx: 'setvar' x, vy: 'setvar' y) {

  return '|-' "( x e. { y | ph } <-> [ x / y ] ph )";
}
