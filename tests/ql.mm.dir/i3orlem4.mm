include "wo.mm";
include "wn.mm";
include "wa.mm";
include "wi3.mm";
include "leo.mm";
include "ler.mm";
include "df-i3.mm";
include "ax-r1.mm";
include "lbtr.mm";

theorem i3orlem4(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvc;
    wo;
    #;
    wn;
    #;
    wvb;
    wvc;
    wo;
    #;
    wa;
    #;
    @3;
    @1;
    @2;
    wn;
    wa;
    #;
    wo;
    #;
    @0;
    @1;
    @2;
    wo;
    wa;
    #;
    wo;
    #;
    @0;
    @2;
    wi3;
    #;
    @3;
    @5;
    @6;
    @3;
    @4;
    leo;
    ler;
    @8;
    @7;
    @0;
    @2;
    df-i3;
    ax-r1;
    lbtr;
  };

  return $|- ( ( a v c ) ' ^ ( b v c ) ) =< ( ( a v c ) ->3 ( b v c ) )$;
}
