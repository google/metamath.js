include "wi2.mm";
include "wo.mm";
include "wa.mm";
include "wi0.mm";
include "comcom.mm";
include "ancom.mm";
include "bctr.mm";
include "gsth2.mm";
include "wn.mm";
include "df-i0.mm";
include "lan.mm";
include "oath1.mm";
include "ax-r2.mm";
include "cbtr.mm";

theorem oacom(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume oacom.1: $|- d C ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) )$;
  assume oacom.2: $|- ( d ^ ( ( b v c ) ->0 ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) C ( a ->2 b )$;





  do {
    wvd;
    wva;
    wvb;
    wi2;
    #;
    wvb;
    wvc;
    wo;
    #;
    @0;
    wva;
    wvc;
    wi2;
    wa;
    #;
    wi0;
    #;
    wa;
    #;
    @2;
    @4;
    wvd;
    @0;
    @3;
    wvd;
    wvd;
    @3;
    oacom.1;
    comcom;
    @3;
    wvd;
    wa;
    #;
    @0;
    @5;
    wvd;
    @3;
    wa;
    @0;
    @3;
    wvd;
    ancom;
    oacom.2;
    bctr;
    comcom;
    gsth2;
    comcom;
    @4;
    @0;
    @1;
    wn;
    @2;
    wo;
    #;
    wa;
    @2;
    @3;
    @6;
    @0;
    @1;
    @2;
    df-i0;
    lan;
    wva;
    wvb;
    wvc;
    oath1;
    ax-r2;
    cbtr;
  };

  return $|-$ $d C ( ( a ->2 b ) ^ ( a ->2 c ) )$;
}
