
axiom ax-3oa(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {

  return $|- ( ( a ->1 c ) ^ ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) =< ( b ->1 c )$;
}
