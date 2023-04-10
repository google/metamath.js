include "wn.mm";
include "wo.mm";
include "wa.mm";
include "wid2.mm";
include "wid1.mm";
include "ax-a2.mm";
include "ax-a1.mm";
include "lor.mm";
include "ax-r2.mm";
include "ancom.mm";
include "2or.mm";
include "2an.mm";
include "df-id2.mm";
include "df-id1.mm";
include "3tr1.mm";

theorem nomcon2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wn;
    #;
    wo;
    #;
    wvb;
    wva;
    wn;
    #;
    @0;
    wa;
    #;
    wo;
    #;
    wa;
    @0;
    @2;
    wn;
    #;
    wo;
    #;
    @0;
    wn;
    #;
    @0;
    @2;
    wa;
    #;
    wo;
    #;
    wa;
    wva;
    wvb;
    wid2;
    @0;
    @2;
    wid1;
    @1;
    @6;
    @4;
    @9;
    @1;
    @0;
    wva;
    wo;
    @6;
    wva;
    @0;
    ax-a2;
    wva;
    @5;
    @0;
    wva;
    ax-a1;
    lor;
    ax-r2;
    wvb;
    @7;
    @3;
    @8;
    wvb;
    ax-a1;
    @2;
    @0;
    ancom;
    2or;
    2an;
    wva;
    wvb;
    df-id2;
    @0;
    @2;
    df-id1;
    3tr1;
  };

  return $|- ( a ==2 b ) = ( b ' ==1 a ' )$;
}
