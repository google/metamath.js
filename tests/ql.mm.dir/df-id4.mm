
axiom df-id4(wva: $term$ a, wvb: $term$ b) {

  return $|- ( a ==4 b ) = ( ( a ' v b ) ^ ( b ' v ( a ^ b ) ) )$;
}
