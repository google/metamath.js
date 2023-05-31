include "wo.mm";
include "wn.mm";
include "wa.mm";
include "wi3.mm";
include "leor.mm";
include "df-i3.mm";
include "ax-r1.mm";
include "lbtr.mm";

theorem i3orlem1(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvc;
    wo;
    #;
    @0;
    wn;
    #;
    wvb;
    wvc;
    wo;
    #;
    wo;
    wa;
    #;
    @1;
    @2;
    wa;
    @1;
    @2;
    wn;
    wa;
    wo;
    #;
    @3;
    wo;
    #;
    @0;
    @2;
    wi3;
    #;
    @3;
    @4;
    leor;
    @6;
    @5;
    @0;
    @2;
    df-i3;
    ax-r1;
    lbtr;
  };

  return $|-$ $( ( a v c ) ^ ( ( a v c ) ' v ( b v c ) ) ) =< ( ( a v c ) ->3 ( b v c ) )$;
}
