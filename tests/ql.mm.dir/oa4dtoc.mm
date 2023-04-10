include "wa.mm";
include "wi1.mm";
include "wo.mm";
include "oatr.mm";

theorem oa4dtoc(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume oa4dtoc.1: $|- ( b ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) =< ( a ' ->1 d )$;





  do {
    wva;
    wvb;
    wva;
    wvb;
    wa;
    wva;
    wvd;
    wi1;
    #;
    wvb;
    wvd;
    wi1;
    #;
    wa;
    wo;
    wva;
    wvc;
    wa;
    @0;
    wvc;
    wvd;
    wi1;
    #;
    wa;
    wo;
    wvb;
    wvc;
    wa;
    @1;
    @2;
    wa;
    wo;
    wa;
    wo;
    wa;
    wvd;
    oa4dtoc.1;
    oatr;
  };

  return $|-$ $( a ' ^ ( a v ( b ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) ) =< d$;
}
