
axiom df-cmtr(wva: $term$ a, wvb: $term$ b) {

  return $|- C ( a , b ) = ( ( ( a ^ b ) v ( a ^ b ' ) ) v ( ( a ' ^ b ) v ( a ' ^ b ' ) ) )$;
}
