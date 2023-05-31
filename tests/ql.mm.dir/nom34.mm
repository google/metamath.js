include "wa.mm";
include "wid4.mm";
include "wid1.mm";
include "wi1.mm";
include "nomb41.mm";
include "nom21.mm";
include "ax-r2.mm";

theorem nom34(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    wid4;
    wva;
    @0;
    wid1;
    wva;
    wvb;
    wi1;
    @0;
    wva;
    nomb41;
    wva;
    wvb;
    nom21;
    ax-r2;
  };

  return $|-$ $( ( a ^ b ) ==4 a ) = ( a ->1 b )$;
}
