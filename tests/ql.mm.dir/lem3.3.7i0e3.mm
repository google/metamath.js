include "nom10.mm";

theorem lem3.3.7i0e3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    nom10;
  };

  return $|-$ $( a ->0 ( a ^ b ) ) = ( a ->1 b )$;
}
