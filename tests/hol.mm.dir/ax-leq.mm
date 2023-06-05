

axiom ax-leq(hal: type al, hbe: type be, vx: var x, ta: term A, tb: term B, tr: term R) {
  assume ax-leq.1: |- "A : be";
  assume ax-leq.2: |- "B : be";
  assume ax-leq.3: |- "R |= ( ( = A ) B )";

  return |- "R |= ( ( = \\ x : al . A ) \\ x : al . B )";
}
