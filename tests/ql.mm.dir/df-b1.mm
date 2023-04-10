
axiom df-b1(wva: $term$ a, wvb: $term$ b) {

  return $|- ( a <->1 b ) = ( ( a ->1 b ) ^ ( b ->1 a ) )$;
}
