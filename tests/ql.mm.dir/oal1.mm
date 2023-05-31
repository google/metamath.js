include "wn.mm";
include "wi2.mm";
include "wo.mm";
include "wa.mm";
include "wi1.mm";
include "oal2.mm";
include "i1i2.mm";
include "df-a.mm";
include "2an.mm";
include "2or.mm";
include "le3tr1.mm";

theorem oal1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wvc;
    wn;
    #;
    wva;
    wn;
    #;
    wi2;
    #;
    @1;
    wvb;
    wn;
    #;
    wo;
    wn;
    #;
    @2;
    @0;
    @3;
    wi2;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    @5;
    wva;
    wvc;
    wi1;
    #;
    wva;
    wvb;
    wa;
    #;
    @8;
    wvb;
    wvc;
    wi1;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    @10;
    @0;
    @1;
    @3;
    oal2;
    @8;
    @2;
    @12;
    @7;
    wva;
    wvc;
    i1i2;
    #;
    @9;
    @4;
    @11;
    @6;
    wva;
    wvb;
    df-a;
    @8;
    @2;
    @10;
    @5;
    @13;
    wvb;
    wvc;
    i1i2;
    #;
    2an;
    2or;
    2an;
    @14;
    le3tr1;
  };

  return $|-$ $( ( a ->1 c ) ^ ( ( a ^ b ) v ( ( a ->1 c ) ^ ( b ->1 c ) ) ) ) =< ( b ->1 c )$;
}
