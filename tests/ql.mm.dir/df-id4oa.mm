
axiom df-id4oa(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {

  return $|-$ $( a == c , d ==OA b ) = ( ( a == d ==OA b ) v ( ( a == d ==OA c ) ^ ( b == d ==OA c ) ) )$;
}
