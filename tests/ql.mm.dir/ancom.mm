include "wn.mm";
include "wo.mm";
include "wa.mm";
include "ax-a2.mm";
include "ax-r4.mm";
include "df-a.mm";
include "3tr1.mm";

theorem ancom(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wvb;
    wn;
    #;
    wo;
    #;
    wn;
    @1;
    @0;
    wo;
    #;
    wn;
    wva;
    wvb;
    wa;
    wvb;
    wva;
    wa;
    @2;
    @3;
    @0;
    @1;
    ax-a2;
    ax-r4;
    wva;
    wvb;
    df-a;
    wvb;
    wva;
    df-a;
    3tr1;
  };

  return $|- ( a ^ b ) = ( b ^ a )$;
}
