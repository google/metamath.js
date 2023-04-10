include "wa.mm";
include "wn.mm";
include "wo.mm";
include "tb.mm";
include "ancom.mm";
include "2or.mm";
include "dfb.mm";
include "3tr1.mm";

theorem bicom(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wa;
    #;
    wo;
    wvb;
    wva;
    wa;
    #;
    @2;
    @1;
    wa;
    #;
    wo;
    wva;
    wvb;
    tb;
    wvb;
    wva;
    tb;
    @0;
    @4;
    @3;
    @5;
    wva;
    wvb;
    ancom;
    @1;
    @2;
    ancom;
    2or;
    wva;
    wvb;
    dfb;
    wvb;
    wva;
    dfb;
    3tr1;
  };

  return $|- ( a == b ) = ( b == a )$;
}
