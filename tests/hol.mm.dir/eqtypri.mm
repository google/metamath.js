

axiom eqtypri(hal: $type$ al, ta: $term$ A, tb: $term$ B, tr: $term$ R) {
  assume eqtypri.1: $|- A : al$;
  assume eqtypri.2: $|- R |= [ B = A ]$;

  return $|- B : al$;
}
