

axiom ax-refl(hal: type al, ta: term A) {
  assume ax-refl.1: |- "A : al";

  return |- "T. |= ( ( = A ) A )";
}
