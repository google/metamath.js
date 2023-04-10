include "wo.mm";
include "wn.mm";
include "wa.mm";
include "wi2.mm";
include "lecon3.mm";
include "ler2an.mm";
include "lelor.mm";
include "df-i2.mm";
include "ax-r1.mm";
include "lbtr.mm";

theorem govar2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume govar.1: $|- a =< b '$;
  assume govar.2: $|- b =< c '$;





  do {
    wva;
    wvb;
    wo;
    wva;
    wvc;
    wn;
    #;
    wva;
    wn;
    #;
    wa;
    #;
    wo;
    #;
    wvc;
    wva;
    wi2;
    #;
    wvb;
    @2;
    wva;
    wvb;
    @0;
    @1;
    govar.2;
    wva;
    wvb;
    govar.1;
    lecon3;
    ler2an;
    lelor;
    @4;
    @3;
    wvc;
    wva;
    df-i2;
    ax-r1;
    lbtr;
  };

  return $|- ( a v b ) =< ( c ->2 a )$;
}
