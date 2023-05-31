include "wa.mm";
include "wn.mm";
include "tb.mm";
include "wo.mm";
include "wt.mm";
include "df-a.mm";
include "con2.mm";
include "2bi.mm";
include "conb.mm";
include "ax-r1.mm";
include "ax-r2.mm";
include "2or.mm";
include "ka4lemo.mm";

theorem ka4lem(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wa;
    #;
    wn;
    #;
    wva;
    wvc;
    wa;
    #;
    wvb;
    wvc;
    wa;
    #;
    tb;
    #;
    wo;
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wo;
    #;
    @5;
    wvc;
    wn;
    #;
    wo;
    #;
    @6;
    @8;
    wo;
    #;
    tb;
    #;
    wo;
    wt;
    @1;
    @7;
    @4;
    @11;
    @0;
    @7;
    wva;
    wvb;
    df-a;
    con2;
    @4;
    @9;
    wn;
    #;
    @10;
    wn;
    #;
    tb;
    #;
    @11;
    @2;
    @12;
    @3;
    @13;
    wva;
    wvc;
    df-a;
    wvb;
    wvc;
    df-a;
    2bi;
    @11;
    @14;
    @9;
    @10;
    conb;
    ax-r1;
    ax-r2;
    2or;
    @5;
    @6;
    @8;
    ka4lemo;
    ax-r2;
  };

  return $|-$ $( ( a ^ b ) ' v ( ( a ^ c ) == ( b ^ c ) ) ) = 1$;
}
