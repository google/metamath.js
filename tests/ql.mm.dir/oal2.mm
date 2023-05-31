include "wn.mm";
include "wi1.mm";
include "wa.mm";
include "wo.mm";
include "wi2.mm";
include "ax-3oa.mm";
include "i2i1.mm";
include "anor3.mm";
include "ax-r1.mm";
include "2an.mm";
include "2or.mm";
include "le3tr1.mm";

theorem oal2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wvb;
    wn;
    #;
    wva;
    wn;
    #;
    wi1;
    #;
    @0;
    wvc;
    wn;
    #;
    wa;
    #;
    @2;
    @3;
    @1;
    wi1;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    @5;
    wva;
    wvb;
    wi2;
    #;
    wvb;
    wvc;
    wo;
    wn;
    #;
    @8;
    wva;
    wvc;
    wi2;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    @10;
    @0;
    @3;
    @1;
    ax-3oa;
    @8;
    @2;
    @12;
    @7;
    wva;
    wvb;
    i2i1;
    #;
    @9;
    @4;
    @11;
    @6;
    @4;
    @9;
    wvb;
    wvc;
    anor3;
    ax-r1;
    @8;
    @2;
    @10;
    @5;
    @13;
    wva;
    wvc;
    i2i1;
    #;
    2an;
    2or;
    2an;
    @14;
    le3tr1;
  };

  return $|-$ $( ( a ->2 b ) ^ ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =< ( a ->2 c )$;
}
