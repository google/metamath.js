include "wa.mm";
include "tb.mm";
include "wi1.mm";
include "bicom.mm";
include "nom25.mm";
include "ax-r2.mm";

theorem nom35(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    tb;
    wva;
    @0;
    tb;
    wva;
    wvb;
    wi1;
    @0;
    wva;
    bicom;
    wva;
    wvb;
    nom25;
    ax-r2;
  };

  return $|-$ $( ( a ^ b ) == a ) = ( a ->1 b )$;
}
