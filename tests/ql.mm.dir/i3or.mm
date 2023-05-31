include "tb.mm";
include "wn.mm";
include "wo.mm";
include "wi3.mm";
include "wt.mm";
include "le1.mm";
include "ka4ot.mm";
include "ax-r1.mm";
include "wa.mm";
include "i3bi.mm";
include "lea.mm";
include "bltr.mm";
include "lelor.mm";
include "lebi.mm";

theorem i3or(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    tb;
    wn;
    #;
    wva;
    wvc;
    wo;
    #;
    wvb;
    wvc;
    wo;
    #;
    wi3;
    #;
    wo;
    #;
    wt;
    @4;
    le1;
    wt;
    @0;
    @1;
    @2;
    tb;
    #;
    wo;
    #;
    @4;
    @6;
    wt;
    wva;
    wvb;
    wvc;
    ka4ot;
    ax-r1;
    @5;
    @3;
    @0;
    @5;
    @3;
    @2;
    @1;
    wi3;
    #;
    wa;
    #;
    @3;
    @8;
    @5;
    @1;
    @2;
    i3bi;
    ax-r1;
    @3;
    @7;
    lea;
    bltr;
    lelor;
    bltr;
    lebi;
  };

  return $|-$ $( ( a == b ) ' v ( ( a v c ) ->3 ( b v c ) ) ) = 1$;
}
