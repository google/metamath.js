
axiom ax-4oa(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {

  return $|- ( ( a ->1 d ) ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) =< ( b ->1 d )$;
}
