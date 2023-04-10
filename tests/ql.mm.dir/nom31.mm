include "wa.mm";
include "wid1.mm";
include "wid4.mm";
include "wi1.mm";
include "nomb41.mm";
include "ax-r1.mm";
include "nom24.mm";
include "ax-r2.mm";

theorem nom31(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    wid1;
    #;
    wva;
    @0;
    wid4;
    #;
    wva;
    wvb;
    wi1;
    @2;
    @1;
    wva;
    @0;
    nomb41;
    ax-r1;
    wva;
    wvb;
    nom24;
    ax-r2;
  };

  return $|- ( ( a ^ b ) ==1 a ) = ( a ->1 b )$;
}
