
axiom df-le(wva: $term$ a, wvb: $term$ b) {

  return $|- ( a =<2 b ) = ( ( a v b ) == b )$;
}
