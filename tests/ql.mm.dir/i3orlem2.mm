include "wa.mm";
include "wo.mm";
include "wi3.mm";
include "leo.mm";
include "le2an.mm";
include "wn.mm";
include "leor.mm";
include "ledi.mm";
include "letr.mm";
include "i3orlem1.mm";

theorem i3orlem2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wa;
    wva;
    wvc;
    wo;
    #;
    wvb;
    wvc;
    wo;
    #;
    wa;
    #;
    @0;
    @1;
    wi3;
    #;
    wva;
    @0;
    wvb;
    @1;
    wva;
    wvc;
    leo;
    wvb;
    wvc;
    leo;
    le2an;
    @2;
    @0;
    @0;
    wn;
    #;
    @1;
    wo;
    wa;
    #;
    @3;
    @2;
    @0;
    @4;
    wa;
    #;
    @2;
    wo;
    @5;
    @2;
    @6;
    leor;
    @0;
    @4;
    @1;
    ledi;
    letr;
    wva;
    wvb;
    wvc;
    i3orlem1;
    letr;
    letr;
  };

  return $|- ( a ^ b ) =< ( ( a v c ) ->3 ( b v c ) )$;
}
