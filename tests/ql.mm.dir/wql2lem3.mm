include "wn.mm";
include "wa.mm";
include "wi2.mm";
include "wo.mm";
include "wt.mm";
include "df-i2.mm";
include "oran2.mm";
include "ax-r1.mm";
include "ran.mm";
include "ancom.mm";
include "ax-r2.mm";
include "lor.mm";
include "wql2lem.mm";
include "omlem2.mm";
include "skr0.mm";
include "3tr.mm";

theorem wql2lem3(wva: $term$ a, wvb: $term$ b) {
  assume wql2lem3.1: $|- ( a ->2 b ) = 1$;





  do {
    wva;
    wvb;
    wn;
    wa;
    #;
    wva;
    wn;
    #;
    wi2;
    @1;
    @0;
    wn;
    #;
    @1;
    wn;
    #;
    wa;
    #;
    wo;
    @1;
    @3;
    @1;
    wvb;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wt;
    @0;
    @1;
    df-i2;
    @4;
    @6;
    @1;
    @4;
    @5;
    @3;
    wa;
    @6;
    @2;
    @5;
    @3;
    @5;
    @2;
    wva;
    wvb;
    oran2;
    ax-r1;
    ran;
    @5;
    @3;
    ancom;
    ax-r2;
    lor;
    @5;
    @7;
    wva;
    wvb;
    wql2lem3.1;
    wql2lem;
    @1;
    wvb;
    omlem2;
    skr0;
    3tr;
  };

  return $|-$ $( ( a ^ b ' ) ->2 a ' ) = 1$;
}
