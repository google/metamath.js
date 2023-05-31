include "wi1.mm";
include "wa.mm";
include "wn.mm";
include "wo.mm";
include "wt.mm";
include "ax-a2.mm";
include "u1lemn1b.mm";
include "2an.mm";
include "ax-r1.mm";
include "lor.mm";
include "df-t.mm";
include "3tr1.mm";

theorem u1lem3var1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvc;
    wi1;
    #;
    wvb;
    wvc;
    wi1;
    #;
    wa;
    #;
    wn;
    #;
    @2;
    wo;
    @2;
    @3;
    wo;
    @3;
    @0;
    wn;
    wvc;
    wi1;
    #;
    @1;
    wn;
    wvc;
    wi1;
    #;
    wa;
    #;
    wo;
    wt;
    @3;
    @2;
    ax-a2;
    @6;
    @2;
    @3;
    @2;
    @6;
    @0;
    @4;
    @1;
    @5;
    wva;
    wvc;
    u1lemn1b;
    wvb;
    wvc;
    u1lemn1b;
    2an;
    ax-r1;
    lor;
    @2;
    df-t;
    3tr1;
  };

  return $|-$ $( ( ( a ->1 c ) ^ ( b ->1 c ) ) ' v ( ( ( a ->1 c ) ' ->1 c ) ^ ( ( b ->1 c ) ' ->1 c ) ) ) = 1$;
}
