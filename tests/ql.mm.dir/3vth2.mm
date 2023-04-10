include "wi2.mm";
include "wo.mm";
include "wn.mm";
include "wa.mm";
include "3vth1.mm";
include "lear.mm";
include "ler2an.mm";
include "ax-a2.mm";
include "ax-r4.mm";
include "lan.mm";
include "bltr.mm";
include "lebi.mm";

theorem 3vth2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wi2;
    #;
    wvb;
    wvc;
    wo;
    #;
    wn;
    #;
    wa;
    #;
    wva;
    wvc;
    wi2;
    #;
    @2;
    wa;
    #;
    @3;
    @4;
    @2;
    wva;
    wvb;
    wvc;
    3vth1;
    @0;
    @2;
    lear;
    ler2an;
    @5;
    @0;
    @2;
    @5;
    @4;
    wvc;
    wvb;
    wo;
    #;
    wn;
    #;
    wa;
    @0;
    @2;
    @7;
    @4;
    @1;
    @6;
    wvb;
    wvc;
    ax-a2;
    ax-r4;
    lan;
    wva;
    wvc;
    wvb;
    3vth1;
    bltr;
    @4;
    @2;
    lear;
    ler2an;
    lebi;
  };

  return $|- ( ( a ->2 b ) ^ ( b v c ) ' ) = ( ( a ->2 c ) ^ ( b v c ) ' )$;
}
