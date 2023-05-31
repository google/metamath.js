include "wa.mm";
include "wi1.mm";
include "wo.mm";
include "oat.mm";

theorem oa4ctod(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume oa4ctod.1: $|- ( a ' ^ ( a v ( b ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) ) =< d$;





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
    oa4ctod.1;
    oat;
  };

  return $|-$ $( b ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) =< ( a ' ->1 d )$;
}
