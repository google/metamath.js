include "tb.mm";
include "wo.mm";
include "wi2.mm";
include "wi1.mm";
include "wa.mm";
include "orbi.mm";
include "i2or.mm";
include "i1or.mm";
include "le2an.mm";
include "bltr.mm";

theorem orbile(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvc;
    tb;
    wvb;
    wvc;
    tb;
    wo;
    wva;
    wvc;
    wi2;
    wvb;
    wvc;
    wi2;
    wo;
    #;
    wvc;
    wva;
    wi1;
    wvc;
    wvb;
    wi1;
    wo;
    #;
    wa;
    wva;
    wvb;
    wa;
    wvc;
    wi2;
    #;
    wvc;
    wva;
    wvb;
    wo;
    wi1;
    #;
    wa;
    wva;
    wvb;
    wvc;
    orbi;
    @0;
    @2;
    @1;
    @3;
    wva;
    wvb;
    wvc;
    i2or;
    wva;
    wvb;
    wvc;
    i1or;
    le2an;
    bltr;
  };

  return $|-$ $( ( a == c ) v ( b == c ) ) =< ( ( ( a ^ b ) ->2 c ) ^ ( c ->1 ( a v b ) ) )$;
}
