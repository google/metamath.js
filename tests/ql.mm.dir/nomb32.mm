include "wn.mm";
include "wo.mm";
include "wa.mm";
include "wid3.mm";
include "wid2.mm";
include "ax-a2.mm";
include "ancom.mm";
include "lor.mm";
include "2an.mm";
include "df-id3.mm";
include "df-id2.mm";
include "3tr1.mm";

theorem nomb32(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wvb;
    wo;
    #;
    wva;
    @0;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    wvb;
    @0;
    wo;
    #;
    wva;
    @2;
    @0;
    wa;
    #;
    wo;
    #;
    wa;
    wva;
    wvb;
    wid3;
    wvb;
    wva;
    wid2;
    @1;
    @5;
    @4;
    @7;
    @0;
    wvb;
    ax-a2;
    @3;
    @6;
    wva;
    @0;
    @2;
    ancom;
    lor;
    2an;
    wva;
    wvb;
    df-id3;
    wvb;
    wva;
    df-id2;
    3tr1;
  };

  return $|- ( a ==3 b ) = ( b ==2 a )$;
}
