
axiom df-id1(wva: $term$ a, wvb: $term$ b) {

  return $|-$ $( a ==1 b ) = ( ( a v b ' ) ^ ( a ' v ( a ^ b ) ) )$;
}
