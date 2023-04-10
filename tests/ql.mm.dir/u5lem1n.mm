include "wi5.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "u5lem1.mm";
include "ancom.mm";
include "df-a.mm";
include "anor2.mm";
include "anor3.mm";
include "2or.mm";
include "ax-r4.mm";
include "ax-r1.mm";
include "ax-r2.mm";
include "con2.mm";

theorem u5lem1n(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi5;
    wva;
    wi5;
    #;
    wva;
    wn;
    #;
    wvb;
    wa;
    #;
    @1;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    @0;
    wva;
    wvb;
    wo;
    #;
    wva;
    @3;
    wo;
    #;
    wa;
    #;
    @5;
    wn;
    #;
    wva;
    wvb;
    u5lem1;
    @8;
    @7;
    @6;
    wa;
    #;
    @9;
    @6;
    @7;
    ancom;
    @10;
    @7;
    wn;
    #;
    @6;
    wn;
    #;
    wo;
    #;
    wn;
    #;
    @9;
    @7;
    @6;
    df-a;
    @9;
    @14;
    @5;
    @13;
    @2;
    @11;
    @4;
    @12;
    wva;
    wvb;
    anor2;
    wva;
    wvb;
    anor3;
    2or;
    ax-r4;
    ax-r1;
    ax-r2;
    ax-r2;
    ax-r2;
    con2;
  };

  return $|- ( ( a ->5 b ) ->5 a ) ' = ( ( a ' ^ b ) v ( a ' ^ b ' ) )$;
}
