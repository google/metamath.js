include "wn.mm";
include "wa.mm";
include "wo.mm";
include "leo.mm";
include "wi1.mm";
include "df-i1.mm";
include "ax-r4.mm";
include "ax-r2.mm";
include "ax-r1.mm";
include "con3.mm";
include "lbtr.mm";

theorem oa6to4h3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d, wve: $term$ e, wvf: $term$ f, wvg: $term$ g) {
  assume oa6to4.1: $|- b ' = ( a ->1 g ) '$;
  assume oa6to4.2: $|- d ' = ( c ->1 g ) '$;
  assume oa6to4.3: $|- f ' = ( e ->1 g ) '$;





  do {
    wve;
    wn;
    #;
    @0;
    wve;
    wvg;
    wa;
    #;
    wo;
    #;
    wvf;
    wn;
    #;
    wn;
    @0;
    @1;
    leo;
    @2;
    @3;
    @3;
    @2;
    wn;
    #;
    @3;
    wve;
    wvg;
    wi1;
    #;
    wn;
    @4;
    oa6to4.3;
    @5;
    @2;
    wve;
    wvg;
    df-i1;
    ax-r4;
    ax-r2;
    ax-r1;
    con3;
    lbtr;
  };

  return $|- e ' =< f ' '$;
}
