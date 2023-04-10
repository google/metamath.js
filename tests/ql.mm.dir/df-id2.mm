
axiom df-id2(wva: $term$ a, wvb: $term$ b) {

  return $|- ( a ==2 b ) = ( ( a v b ' ) ^ ( b v ( a ' ^ b ' ) ) )$;
}
