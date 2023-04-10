include "wn.mm";
include "wi1.mm";
include "wa.mm";
include "wo.mm";
include "ax-3oa.mm";
include "u1lem11.mm";
include "ax-a2.mm";
include "2an.mm";
include "ax-r5.mm";
include "ax-r2.mm";
include "le3tr2.mm";

theorem 3oa2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wn;
    wvc;
    wi1;
    #;
    wvc;
    wi1;
    #;
    @0;
    wvb;
    wn;
    wvc;
    wi1;
    #;
    wa;
    #;
    @1;
    @2;
    wvc;
    wi1;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    @4;
    wva;
    wvc;
    wi1;
    #;
    @7;
    wvb;
    wvc;
    wi1;
    #;
    wa;
    #;
    @3;
    wo;
    #;
    wa;
    @8;
    @0;
    @2;
    wvc;
    ax-3oa;
    @1;
    @7;
    @6;
    @10;
    wva;
    wvc;
    u1lem11;
    #;
    @6;
    @5;
    @3;
    wo;
    @10;
    @3;
    @5;
    ax-a2;
    @5;
    @9;
    @3;
    @1;
    @7;
    @4;
    @8;
    @11;
    wvb;
    wvc;
    u1lem11;
    #;
    2an;
    ax-r5;
    ax-r2;
    2an;
    @12;
    le3tr2;
  };

  return $|- ( ( a ->1 c ) ^ ( ( ( a ->1 c ) ^ ( b ->1 c ) ) v ( ( a ' ->1 c ) ^ ( b ' ->1 c ) ) ) ) =< ( b ->1 c )$;
}
