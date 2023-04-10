
axiom ax-r3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume r3.1: $|- ( c v c ' ) = ( ( a ' v b ' ) ' v ( a v b ) ' )$;

  return $|- a = b$;
}
