include "wa.mm";
include "wo.mm";
include "ledio.mm";
include "ax-a2.mm";
include "2an.mm";
include "le3tr1.mm";

theorem ledior(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wvc;
    wa;
    #;
    wo;
    wva;
    wvb;
    wo;
    #;
    wva;
    wvc;
    wo;
    #;
    wa;
    @0;
    wva;
    wo;
    wvb;
    wva;
    wo;
    #;
    wvc;
    wva;
    wo;
    #;
    wa;
    wva;
    wvb;
    wvc;
    ledio;
    @0;
    wva;
    ax-a2;
    @3;
    @1;
    @4;
    @2;
    wvb;
    wva;
    ax-a2;
    wvc;
    wva;
    ax-a2;
    2an;
    le3tr1;
  };

  return $|-$ $( ( b ^ c ) v a ) =< ( ( b v a ) ^ ( c v a ) )$;
}
