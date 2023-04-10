include "u12lem.mm";

theorem lem4.6.6i1j2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    u12lem;
  };

  return $|- ( ( a ->1 b ) v ( a ->2 b ) ) = ( a ->0 b )$;
}
