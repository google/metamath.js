include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "wa.mm";
include "u3lemaa.mm";
include "oran2.mm";
include "lan.mm";
include "ax-r2.mm";
include "df-a.mm";
include "anor1.mm";
include "3tr2.mm";
include "con1.mm";

theorem u3lemnona(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi3;
    #;
    wn;
    wva;
    wn;
    #;
    wo;
    #;
    @1;
    wva;
    wvb;
    wn;
    wa;
    #;
    wo;
    #;
    @0;
    wva;
    wa;
    #;
    wva;
    @3;
    wn;
    #;
    wa;
    #;
    @2;
    wn;
    @4;
    wn;
    @5;
    wva;
    @1;
    wvb;
    wo;
    #;
    wa;
    @7;
    wva;
    wvb;
    u3lemaa;
    @8;
    @6;
    wva;
    wva;
    wvb;
    oran2;
    lan;
    ax-r2;
    @0;
    wva;
    df-a;
    wva;
    @3;
    anor1;
    3tr2;
    con1;
  };

  return $|-$ $( ( a ->3 b ) ' v a ' ) = ( a ' v ( a ^ b ' ) )$;
}
