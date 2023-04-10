include "wn.mm";
include "wa.mm";
include "wo.mm";
include "df-a.mm";
include "ax-a1.mm";
include "ax-r1.mm";
include "lor.mm";
include "ax-r4.mm";
include "ax-r2.mm";

theorem anor1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wn;
    #;
    wa;
    wva;
    wn;
    #;
    @0;
    wn;
    #;
    wo;
    #;
    wn;
    @1;
    wvb;
    wo;
    #;
    wn;
    wva;
    @0;
    df-a;
    @3;
    @4;
    @2;
    wvb;
    @1;
    wvb;
    @2;
    wvb;
    ax-a1;
    ax-r1;
    lor;
    ax-r4;
    ax-r2;
  };

  return $|- ( a ^ b ' ) = ( a ' v b ) '$;
}
