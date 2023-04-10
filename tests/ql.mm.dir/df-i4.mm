
axiom df-i4(wva: $term$ a, wvb: $term$ b) {

  return $|-$ $( a ->4 b ) = ( ( ( a ^ b ) v ( a ' ^ b ) ) v ( ( a ' v b ) ^ b ' ) )$;
}
