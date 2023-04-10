
axiom df-id3(wva: $term$ a, wvb: $term$ b) {

  return $|- ( a ==3 b ) = ( ( a ' v b ) ^ ( a v ( a ' ^ b ' ) ) )$;
}
