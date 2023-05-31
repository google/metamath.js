include "wo.mm";
include "wa.mm";
include "wn.mm";
include "wi2.mm";
include "oa4lem1.mm";
include "oa4lem2.mm";
include "le2an.mm";
include "leor.mm";
include "letr.mm";

theorem oa4lem3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume oa4lem1.1: $|- a =< b '$;
  assume oa4lem1.2: $|- c =< d '$;





  do {
    wva;
    wvb;
    wo;
    #;
    wvc;
    wvd;
    wo;
    #;
    wa;
    wva;
    wvc;
    wo;
    wn;
    #;
    wvb;
    wi2;
    #;
    @2;
    wvd;
    wi2;
    #;
    wa;
    #;
    wvb;
    wvd;
    wo;
    wn;
    #;
    @5;
    wo;
    @0;
    @3;
    @1;
    @4;
    wva;
    wvb;
    wvc;
    wvd;
    oa4lem1.1;
    oa4lem1.2;
    oa4lem1;
    wva;
    wvb;
    wvc;
    wvd;
    oa4lem1.1;
    oa4lem1.2;
    oa4lem2;
    le2an;
    @5;
    @6;
    leor;
    letr;
  };

  return $|-$ $( ( a v b ) ^ ( c v d ) ) =< ( ( b v d ) ' v ( ( ( a v c ) ' ->2 b ) ^ ( ( a v c ) ' ->2 d ) ) )$;
}
