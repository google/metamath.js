include "wo.mm";
include "wa.mm";
include "ax-a2.mm";
include "ax-r5.mm";
include "lor.mm";
include "2an.mm";
include "wn.mm";
include "ax-r4.mm";
include "le3tr1.mm";
include "mhlemlem1.mm";
include "ax-r2.mm";

theorem mhlemlem2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume mhlem.1: $|- ( a v b ) =< ( c v d ) '$;





  do {
    wva;
    wvb;
    wo;
    #;
    wvd;
    wo;
    #;
    wvb;
    wvc;
    wvd;
    wo;
    #;
    wo;
    #;
    wa;
    wvb;
    wva;
    wo;
    #;
    wvd;
    wo;
    #;
    wvb;
    wvd;
    wvc;
    wo;
    #;
    wo;
    #;
    wa;
    wvb;
    wvd;
    wo;
    @1;
    @5;
    @3;
    @7;
    @0;
    @4;
    wvd;
    wva;
    wvb;
    ax-a2;
    ax-r5;
    @2;
    @6;
    wvb;
    wvc;
    wvd;
    ax-a2;
    lor;
    2an;
    wvb;
    wva;
    wvd;
    wvc;
    @0;
    @2;
    wn;
    @4;
    @6;
    wn;
    mhlem.1;
    wvb;
    wva;
    ax-a2;
    @6;
    @2;
    wvd;
    wvc;
    ax-a2;
    ax-r4;
    le3tr1;
    mhlemlem1;
    ax-r2;
  };

  return $|- ( ( ( a v b ) v d ) ^ ( b v ( c v d ) ) ) = ( b v d )$;
}
