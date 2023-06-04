

axiom eqtypi(hal: type al, ta: term A, tb: term B, tr: term R) {
  assume eqcomi.1: |- "A : al";
  assume eqcomi.2: |- "R |= [ A = B ]";

  return '|-' "B : al";
}
