
axiom df-i5(wva: $term$ a, wvb: $term$ b) {

  return $|- ( a ->5 b ) = ( ( ( a ^ b ) v ( a ' ^ b ) ) v ( a ' ^ b ' ) )$;
}
