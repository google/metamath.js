include "wo.mm";
include "wn.mm";
include "wa.mm";
include "wi2.mm";
include "leo.mm";
include "ax-a1.mm";
include "lbtr.mm";
include "ler2an.mm";
include "lelor.mm";
include "ax-a2.mm";
include "df-i2.mm";
include "le3tr1.mm";

theorem oa4lem1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume oa4lem1.1: $|- a =< b '$;
  assume oa4lem1.2: $|- c =< d '$;





  do {
    wvb;
    wva;
    wo;
    wvb;
    wva;
    wvc;
    wo;
    #;
    wn;
    #;
    wn;
    #;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    wva;
    wvb;
    wo;
    @1;
    wvb;
    wi2;
    wva;
    @4;
    wvb;
    wva;
    @2;
    @3;
    wva;
    @0;
    @2;
    wva;
    wvc;
    leo;
    @0;
    ax-a1;
    lbtr;
    oa4lem1.1;
    ler2an;
    lelor;
    wva;
    wvb;
    ax-a2;
    @1;
    wvb;
    df-i2;
    le3tr1;
  };

  return $|-$ $( a v b ) =< ( ( a v c ) ' ->2 b )$;
}
