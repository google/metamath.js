
axiom df-i3(wva: $term$ a, wvb: $term$ b) {

  return $|- ( a ->3 b ) = ( ( ( a ' ^ b ) v ( a ' ^ b ' ) ) v ( a ^ ( a ' v b ) ) )$;
}
