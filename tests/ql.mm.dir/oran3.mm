include "wn.mm";
include "wo.mm";
include "wa.mm";
include "df-a.mm";
include "ax-r1.mm";
include "con3.mm";

theorem oran3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    wvb;
    wn;
    wo;
    #;
    wva;
    wvb;
    wa;
    #;
    @1;
    @0;
    wn;
    wva;
    wvb;
    df-a;
    ax-r1;
    con3;
  };

  return $|- ( a ' v b ' ) = ( a ^ b ) '$;
}
