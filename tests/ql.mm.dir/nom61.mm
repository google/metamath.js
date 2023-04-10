include "wo.mm";
include "wid1.mm";
include "wid4.mm";
include "wi2.mm";
include "nomb41.mm";
include "ax-r1.mm";
include "nom54.mm";
include "ax-r2.mm";

theorem nom61(wva: $term$ a, wvb: $term$ b) {





  do {
    wvb;
    wva;
    wvb;
    wo;
    #;
    wid1;
    #;
    @0;
    wvb;
    wid4;
    #;
    wva;
    wvb;
    wi2;
    @2;
    @1;
    @0;
    wvb;
    nomb41;
    ax-r1;
    wva;
    wvb;
    nom54;
    ax-r2;
  };

  return $|-$ $( b ==1 ( a v b ) ) = ( a ->2 b )$;
}
