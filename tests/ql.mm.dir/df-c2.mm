
axiom df-c2(wva: $term$ a, wvb: $term$ b) {
  assume df-c2.1: $|- a C b$;

  return $|-$ $a = ( ( a ^ b ) v ( a ^ b ' ) )$;
}
