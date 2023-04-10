include "wo.mm";
include "wi2.mm";
include "wa.mm";
include "wi0.mm";
include "lear.mm";
include "letr.mm";
include "lecom.mm";
include "lea.mm";
include "oacom.mm";

theorem oacom2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume oacom2.1: $|- d =< ( ( a ->2 b ) ^ ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) )$;





  do {
    wva;
    wvb;
    wvc;
    wvd;
    wvd;
    wvb;
    wvc;
    wo;
    wva;
    wvb;
    wi2;
    #;
    wva;
    wvc;
    wi2;
    wa;
    wi0;
    #;
    wvd;
    @0;
    @1;
    wa;
    #;
    @1;
    oacom2.1;
    @0;
    @1;
    lear;
    letr;
    lecom;
    wvd;
    @1;
    wa;
    #;
    @0;
    @3;
    wvd;
    @0;
    wvd;
    @1;
    lea;
    wvd;
    @2;
    @0;
    oacom2.1;
    @0;
    @1;
    lea;
    letr;
    letr;
    lecom;
    oacom;
  };

  return $|-$ $d C ( ( a ->2 b ) ^ ( a ->2 c ) )$;
}
