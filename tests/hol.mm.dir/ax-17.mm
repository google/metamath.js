

axiom ax-17(hal: 'type' al, hbe: 'type' be, vx: 'var' x, ta: 'term' A, tb: 'term' B) {
  assume ax-17.1: |- "A : be";
  assume ax-17.2: |- "B : al";

  return '|-' "T. |= [ ( \\ x : al . A B ) = A ]";
}
