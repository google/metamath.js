include "wn.mm";
include "wo.mm";
include "wa.mm";
include "wid4.mm";
include "wid1.mm";
include "ax-a2.mm";
include "ancom.mm";
include "lor.mm";
include "2an.mm";
include "df-id4.mm";
include "df-id1.mm";
include "3tr1.mm";

theorem nomb41(wva: $term$ a, wvb: $term$ b) {





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
    wvb;
    wa;
    #;
    wo;
    #;
    wa;
    wvb;
    @0;
    wo;
    #;
    @2;
    wvb;
    wva;
    wa;
    #;
    wo;
    #;
    wa;
    wva;
    wvb;
    wid4;
    wvb;
    wva;
    wid1;
    @1;
    @5;
    @4;
    @7;
    @0;
    wvb;
    ax-a2;
    @3;
    @6;
    @2;
    wva;
    wvb;
    ancom;
    lor;
    2an;
    wva;
    wvb;
    df-id4;
    wvb;
    wva;
    df-id1;
    3tr1;
  };

  return $|-$ $( a ==4 b ) = ( b ==1 a )$;
}
