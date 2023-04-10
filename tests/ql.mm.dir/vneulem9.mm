include "wo.mm";
include "wa.mm";
include "ancom.mm";
include "vneulem5.mm";
include "ax-r2.mm";
include "orcom.mm";
include "vneulem4.mm";
include "ror.mm";
include "3tr.mm";

theorem vneulem9(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume vneulem6.1: $|- ( ( a v b ) ^ ( c v d ) ) = 0$;





  do {
    wva;
    wvb;
    wo;
    #;
    wvd;
    wo;
    #;
    @0;
    wvc;
    wo;
    #;
    wa;
    #;
    @0;
    @2;
    wvd;
    wa;
    #;
    wo;
    #;
    @4;
    @0;
    wo;
    wvc;
    wvd;
    wa;
    #;
    @0;
    wo;
    @3;
    @2;
    @1;
    wa;
    @5;
    @1;
    @2;
    ancom;
    wvc;
    wvd;
    wva;
    wvb;
    vneulem5;
    ax-r2;
    @0;
    @4;
    orcom;
    @4;
    @6;
    @0;
    wvc;
    wvd;
    wva;
    wvb;
    vneulem6.1;
    vneulem4;
    ror;
    3tr;
  };

  return $|- ( ( ( a v b ) v d ) ^ ( ( a v b ) v c ) ) = ( ( c ^ d ) v ( a v b ) )$;
}
