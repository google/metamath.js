
axiom ax-oal4(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume oal4.1: $|- a =< b '$;
  assume oal4.2: $|- c =< d '$;

  return $|-$ $( ( a v b ) ^ ( c v d ) ) =< ( b v ( a ^ ( c v ( ( a v c ) ^ ( b v d ) ) ) ) )$;
}
