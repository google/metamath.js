include "wo.mm";
include "wa.mm";
include "wancom.mm";
include "wddi1.mm";
include "w2or.mm";
include "wr2.mm";

theorem wddi2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wo;
    #;
    wvc;
    wa;
    wvc;
    @0;
    wa;
    #;
    wva;
    wvc;
    wa;
    #;
    wvb;
    wvc;
    wa;
    #;
    wo;
    #;
    @0;
    wvc;
    wancom;
    @1;
    wvc;
    wva;
    wa;
    #;
    wvc;
    wvb;
    wa;
    #;
    wo;
    @4;
    wvc;
    wva;
    wvb;
    wddi1;
    @5;
    @2;
    @6;
    @3;
    wvc;
    wva;
    wancom;
    wvc;
    wvb;
    wancom;
    w2or;
    wr2;
    wr2;
  };

  return $|- ( ( ( a v b ) ^ c ) == ( ( a ^ c ) v ( b ^ c ) ) ) = 1$;
}
