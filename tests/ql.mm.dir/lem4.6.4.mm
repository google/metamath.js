include "u1lem12.mm";

theorem lem4.6.4(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    u1lem12;
  };

  return $|- ( ( a ->1 b ) ->1 b ) = ( a ' ->1 b )$;
}
