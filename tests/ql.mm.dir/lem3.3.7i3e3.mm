include "nom13.mm";

theorem lem3.3.7i3e3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    nom13;
  };

  return $|-$ $( a ->3 ( a ^ b ) ) = ( a ->1 b )$;
}
