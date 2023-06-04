

axiom ax-eqmp(ta: 'term' A, tb: 'term' B, tr: 'term' R) {
  assume ax-eqmp.1: |- "R |= A";
  assume ax-eqmp.2: |- "R |= ( ( = A ) B )";

  return '|-' "R |= B";
}
