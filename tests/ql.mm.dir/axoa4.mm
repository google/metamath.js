include "wn.mm";
include "wa.mm";
include "wi1.mm";
include "wo.mm";
include "u1lem9b.mm";
include "leran.mm";
include "ax-4oa.mm";
include "id.mm";
include "oa4gto4u.mm";
include "oa4uto4.mm";
include "letr.mm";

theorem axoa4(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {





  do {
    wva;
    wn;
    #;
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
    @1;
    wvc;
    wvd;
    wi1;
    #;
    wa;
    wo;
    wvb;
    wvc;
    wa;
    @2;
    @3;
    wa;
    wo;
    wa;
    wo;
    wa;
    wo;
    #;
    wa;
    @1;
    @4;
    wa;
    wvd;
    @0;
    @1;
    @4;
    wva;
    wvd;
    u1lem9b;
    leran;
    wva;
    wvb;
    wvc;
    wvd;
    wva;
    wvb;
    wvc;
    wvd;
    @2;
    @1;
    @3;
    @2;
    @1;
    @3;
    wvd;
    ax-4oa;
    @1;
    id;
    @2;
    id;
    @3;
    id;
    oa4gto4u;
    oa4uto4;
    letr;
  };

  return $|-$ $( a ' ^ ( a v ( b ^ ( ( ( a ^ b ) v ( ( a ->1 d ) ^ ( b ->1 d ) ) ) v ( ( ( a ^ c ) v ( ( a ->1 d ) ^ ( c ->1 d ) ) ) ^ ( ( b ^ c ) v ( ( b ->1 d ) ^ ( c ->1 d ) ) ) ) ) ) ) ) =< d$;
}
