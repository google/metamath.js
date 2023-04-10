include "wi2.mm";
include "wo.mm";
include "wn.mm";
include "wa.mm";
include "lea.mm";
include "ler2an.mm";
include "2oath1.mm";
include "lbtr.mm";
include "lear.mm";
include "letr.mm";

theorem oaeqv(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume oaeqv.1: $|- ( ( a ->2 b ) ^ ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =< ( ( b v c ) ->2 ( ( a ->2 b ) ^ ( a ->2 c ) ) )$;





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
    @0;
    wva;
    wvc;
    wi2;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    #;
    @3;
    @2;
    @5;
    @0;
    @1;
    @3;
    wi2;
    #;
    wa;
    @3;
    @5;
    @0;
    @6;
    @0;
    @4;
    lea;
    oaeqv.1;
    ler2an;
    wva;
    wvb;
    wvc;
    2oath1;
    lbtr;
    @0;
    @2;
    lear;
    letr;
  };

  return $|- ( ( a ->2 b ) ^ ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =< ( a ->2 c )$;
}
