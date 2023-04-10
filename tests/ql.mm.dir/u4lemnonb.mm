include "wi4.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "u4lemab.mm";
include "ax-a2.mm";
include "anor2.mm";
include "df-a.mm";
include "2or.mm";
include "ax-r2.mm";
include "oran3.mm";
include "3tr2.mm";
include "con1.mm";

theorem u4lemnonb(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi4;
    #;
    wn;
    wvb;
    wn;
    #;
    wo;
    #;
    wva;
    @1;
    wo;
    #;
    wva;
    wn;
    #;
    @1;
    wo;
    #;
    wa;
    #;
    @0;
    wvb;
    wa;
    #;
    @3;
    wn;
    #;
    @5;
    wn;
    #;
    wo;
    #;
    @2;
    wn;
    @6;
    wn;
    @7;
    wva;
    wvb;
    wa;
    #;
    @4;
    wvb;
    wa;
    #;
    wo;
    #;
    @10;
    wva;
    wvb;
    u4lemab;
    @13;
    @12;
    @11;
    wo;
    @10;
    @11;
    @12;
    ax-a2;
    @12;
    @8;
    @11;
    @9;
    wva;
    wvb;
    anor2;
    wva;
    wvb;
    df-a;
    2or;
    ax-r2;
    ax-r2;
    @0;
    wvb;
    df-a;
    @3;
    @5;
    oran3;
    3tr2;
    con1;
  };

  return $|- ( ( a ->4 b ) ' v b ' ) = ( ( a v b ' ) ^ ( a ' v b ' ) )$;
}
