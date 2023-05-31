include "wa.mm";
include "wo.mm";
include "wa2.mm";
include "wddi3.mm";
include "w2an.mm";
include "wr2.mm";

theorem wddi4(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wa;
    #;
    wvc;
    wo;
    wvc;
    @0;
    wo;
    #;
    wva;
    wvc;
    wo;
    #;
    wvb;
    wvc;
    wo;
    #;
    wa;
    #;
    @0;
    wvc;
    wa2;
    @1;
    wvc;
    wva;
    wo;
    #;
    wvc;
    wvb;
    wo;
    #;
    wa;
    @4;
    wvc;
    wva;
    wvb;
    wddi3;
    @5;
    @2;
    @6;
    @3;
    wvc;
    wva;
    wa2;
    wvc;
    wvb;
    wa2;
    w2an;
    wr2;
    wr2;
  };

  return $|-$ $( ( ( a ^ b ) v c ) == ( ( a v c ) ^ ( b v c ) ) ) = 1$;
}
