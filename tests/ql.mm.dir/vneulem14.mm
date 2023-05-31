include "wa.mm";
include "wo.mm";
include "vneulem12.mm";
include "vneulem13.mm";
include "tr.mm";

theorem vneulem14(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume vneulem13.1: $|- ( ( a v b ) ^ ( c v d ) ) = 0$;





  do {
    wvc;
    wvd;
    wa;
    #;
    wva;
    wvb;
    wo;
    #;
    wo;
    wvc;
    wvd;
    wo;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    wa;
    @0;
    @1;
    @3;
    wa;
    wo;
    @0;
    @2;
    wo;
    wva;
    wvb;
    wvc;
    wvd;
    vneulem12;
    wva;
    wvb;
    wvc;
    wvd;
    vneulem13.1;
    vneulem13;
    tr;
  };

  return $|-$ $( ( ( c ^ d ) v ( a v b ) ) ^ ( ( c v d ) v ( a ^ b ) ) ) = ( ( c ^ d ) v ( a ^ b ) )$;
}
