include "nom15.mm";

theorem lem3.3.7i5e3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    nom15;
  };

  return $|- ( a ->5 ( a ^ b ) ) = ( a ->1 b )$;
}
