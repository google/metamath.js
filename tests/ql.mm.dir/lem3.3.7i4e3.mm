include "nom14.mm";

theorem lem3.3.7i4e3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    nom14;
  };

  return $|- ( a ->4 ( a ^ b ) ) = ( a ->1 b )$;
}
