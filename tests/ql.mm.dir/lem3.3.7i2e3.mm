include "nom12.mm";

theorem lem3.3.7i2e3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    nom12;
  };

  return $|- ( a ->2 ( a ^ b ) ) = ( a ->1 b )$;
}
