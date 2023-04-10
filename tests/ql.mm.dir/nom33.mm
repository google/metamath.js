include "wa.mm";
include "wid3.mm";
include "wid2.mm";
include "wi1.mm";
include "nomb32.mm";
include "nom22.mm";
include "ax-r2.mm";

theorem nom33(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    wid3;
    wva;
    @0;
    wid2;
    wva;
    wvb;
    wi1;
    @0;
    wva;
    nomb32;
    wva;
    wvb;
    nom22;
    ax-r2;
  };

  return $|-$ $( ( a ^ b ) ==3 a ) = ( a ->1 b )$;
}
