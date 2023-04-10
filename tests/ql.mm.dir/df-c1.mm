
axiom df-c1(wva: $term$ a, wvb: $term$ b) {
  assume df-c1.1: $|- a = ( ( a ^ b ) v ( a ^ b ' ) )$;

  return $|-$ $a C b$;
}
