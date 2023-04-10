
axiom ax-ml(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {

  return $|-$ $( ( a v b ) ^ ( a v c ) ) =< ( a v ( b ^ ( a v c ) ) )$;
}
