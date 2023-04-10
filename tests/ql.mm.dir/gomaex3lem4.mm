include "wo.mm";
include "wn.mm";
include "wa.mm";
include "leor.mm";
include "wi1.mm";
include "ax-a1.mm";
include "df-i1.mm";
include "ax-r1.mm";
include "ax-r4.mm";
include "3tr1.mm";
include "lbtr.mm";

theorem gomaex3lem4(wva: $term$ a, wvb: $term$ b, wvd: $term$ d, wve: $term$ e, wvp: $term$ p) {
  assume gomaex3lem4.9: $|- p = ( ( a v b ) ->1 ( d v e ) ' ) '$;





  do {
    wva;
    wvb;
    wo;
    #;
    wvd;
    wve;
    wo;
    wn;
    #;
    wa;
    #;
    @0;
    wn;
    #;
    @2;
    wo;
    #;
    wvp;
    wn;
    #;
    @2;
    @3;
    leor;
    @0;
    @1;
    wi1;
    #;
    @6;
    wn;
    #;
    wn;
    @4;
    @5;
    @6;
    ax-a1;
    @6;
    @4;
    @0;
    @1;
    df-i1;
    ax-r1;
    wvp;
    @7;
    gomaex3lem4.9;
    ax-r4;
    3tr1;
    lbtr;
  };

  return $|-$ $( ( a v b ) ^ ( d v e ) ' ) =< p '$;
}
