include "wi1.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "df-i1.mm";
include "df-a.mm";
include "ax-r1.mm";
include "lor.mm";
include "ax-r4.mm";
include "ax-r2.mm";
include "con3.mm";
include "con2.mm";

theorem ud1lem0c(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi1;
    #;
    wva;
    wva;
    wn;
    #;
    wvb;
    wn;
    wo;
    #;
    wa;
    #;
    @0;
    @1;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    @3;
    wn;
    wva;
    wvb;
    df-i1;
    @5;
    @3;
    @3;
    @5;
    wn;
    #;
    @3;
    @1;
    @2;
    wn;
    #;
    wo;
    #;
    wn;
    @6;
    wva;
    @2;
    df-a;
    @8;
    @5;
    @7;
    @4;
    @1;
    @4;
    @7;
    wva;
    wvb;
    df-a;
    ax-r1;
    lor;
    ax-r4;
    ax-r2;
    ax-r1;
    con3;
    ax-r2;
    con2;
  };

  return $|-$ $( a ->1 b ) ' = ( a ^ ( a ' v b ' ) )$;
}
