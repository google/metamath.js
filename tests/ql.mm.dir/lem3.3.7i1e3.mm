include "nom11.mm";

theorem lem3.3.7i1e3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    nom11;
  };

  return $|-$ $( a ->1 ( a ^ b ) ) = ( a ->1 b )$;
}
