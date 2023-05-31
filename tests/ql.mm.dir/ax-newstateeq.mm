
axiom ax-newstateeq(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {

  return $|-$ $( ( ( a ->1 b ) ->1 ( c ->1 b ) ) ^ ( ( a ->1 c ) ^ ( b ->1 a ) ) ) =< ( c ->1 a )$;
}
