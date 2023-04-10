include "u1lem9b.mm";

theorem lem4.6.3le2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    u1lem9b;
  };

  return $|- a ' =< ( a ->1 b )$;
}
