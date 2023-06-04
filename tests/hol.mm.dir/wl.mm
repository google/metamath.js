

axiom wl(hal: 'type' al, hbe: 'type' be, vx: 'var' x, tt: 'term' T) {
  assume wl.1: |- "T : be";

  return '|-' "\\ x : al . T : ( al -> be )";
}
