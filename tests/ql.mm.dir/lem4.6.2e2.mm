include "u1lemab.mm";

theorem lem4.6.2e2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    u1lemab;
  };

  return $|- ( ( a ->1 b ) ^ b ) = ( ( a ^ b ) v ( a ' ^ b ) )$;
}
