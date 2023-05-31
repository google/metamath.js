
axiom df-id3oa(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {

  return $|-$ $( a == c ==OA b ) = ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) )$;
}
