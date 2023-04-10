include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wid0.mm";
include "ancom.mm";
include "df-id0.mm";
include "3tr1.mm";

theorem lem3.3.7i0e2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    @0;
    wn;
    wva;
    wo;
    #;
    wa;
    @2;
    @1;
    wa;
    wva;
    @0;
    wid0;
    @0;
    wva;
    wid0;
    @1;
    @2;
    ancom;
    wva;
    @0;
    df-id0;
    @0;
    wva;
    df-id0;
    3tr1;
  };

  return $|-$ $( a ==0 ( a ^ b ) ) = ( ( a ^ b ) ==0 a )$;
}
