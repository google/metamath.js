include "wn.mm";
include "wo.mm";
include "wa.mm";
include "anorabs2.mm";
include "ax-a2.mm";
include "lan.mm";
include "lor.mm";
include "3tr1.mm";

theorem anorabs(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wvb;
    @0;
    wvb;
    wva;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    @2;
    @0;
    wvb;
    @0;
    wva;
    wvb;
    wo;
    #;
    wa;
    #;
    wo;
    #;
    wa;
    @5;
    @0;
    wvb;
    wva;
    anorabs2;
    @6;
    @3;
    @0;
    @5;
    @2;
    wvb;
    @4;
    @1;
    @0;
    wva;
    wvb;
    ax-a2;
    lan;
    #;
    lor;
    lan;
    @7;
    3tr1;
  };

  return $|-$ $( a ' ^ ( b v ( a ' ^ ( a v b ) ) ) ) = ( a ' ^ ( a v b ) )$;
}
