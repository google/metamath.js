include "wn.mm";
include "wo.mm";
include "wa.mm";
include "wid0.mm";
include "ax-a2.mm";
include "ax-a1.mm";
include "ax-r5.mm";
include "ax-r2.mm";
include "2an.mm";
include "df-id0.mm";
include "3tr1.mm";

theorem nomcon0(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wvb;
    wo;
    #;
    wvb;
    wn;
    #;
    wva;
    wo;
    #;
    wa;
    @2;
    wn;
    #;
    @0;
    wo;
    #;
    @0;
    wn;
    #;
    @2;
    wo;
    #;
    wa;
    wva;
    wvb;
    wid0;
    @2;
    @0;
    wid0;
    @1;
    @5;
    @3;
    @7;
    @1;
    wvb;
    @0;
    wo;
    @5;
    @0;
    wvb;
    ax-a2;
    wvb;
    @4;
    @0;
    wvb;
    ax-a1;
    ax-r5;
    ax-r2;
    @3;
    wva;
    @2;
    wo;
    @7;
    @2;
    wva;
    ax-a2;
    wva;
    @6;
    @2;
    wva;
    ax-a1;
    ax-r5;
    ax-r2;
    2an;
    wva;
    wvb;
    df-id0;
    @2;
    @0;
    df-id0;
    3tr1;
  };

  return $|-$ $( a ==0 b ) = ( b ' ==0 a ' )$;
}
