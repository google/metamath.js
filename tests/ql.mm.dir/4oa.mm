include "wi1.mm";
include "wa.mm";
include "wo.mm";
include "lan.mm";
include "wn.mm";
include "axoa4a.mm";
include "id.mm";
include "oa4to4u2.mm";
include "oa4uto4g.mm";
include "bltr.mm";

theorem 4oa(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d, wve: $term$ e, wvf: $term$ f) {
  assume 4oa.1: $|- e = ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) )$;
  assume 4oa.2: $|- f = ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v e )$;





  do {
    wva;
    wvd;
    wi1;
    #;
    wvf;
    wa;
    @0;
    wva;
    wvb;
    wa;
    @0;
    wvb;
    wvd;
    wi1;
    #;
    wa;
    wo;
    wve;
    wo;
    #;
    wa;
    @1;
    wvf;
    @2;
    @0;
    4oa.2;
    lan;
    wva;
    wvb;
    wvc;
    wvd;
    wve;
    wvb;
    wn;
    #;
    wva;
    wn;
    #;
    wvc;
    wn;
    #;
    wvd;
    @3;
    wn;
    wvd;
    wi1;
    #;
    @4;
    wn;
    wvd;
    wi1;
    #;
    @5;
    wn;
    wvd;
    wi1;
    #;
    @6;
    @7;
    @8;
    wvd;
    axoa4a;
    @6;
    id;
    @7;
    id;
    @8;
    id;
    oa4to4u2;
    4oa.1;
    oa4uto4g;
    bltr;
  };

  return $|-$ $( ( a ->1 d ) ^ f ) =< ( b ->1 d )$;
}
