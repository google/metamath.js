include "wi1.mm";
include "wi2.mm";
include "wi0.mm";
include "wn.mm";
include "wo.mm";
include "wt.mm";
include "df-i0.mm";
include "woml6.mm";
include "ax-r2.mm";

theorem lem3.4.1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wi1;
    #;
    wva;
    wvb;
    wi2;
    #;
    wi0;
    @0;
    wn;
    @1;
    wo;
    wt;
    @0;
    @1;
    df-i0;
    wva;
    wvb;
    woml6;
    ax-r2;
  };

  return $|- ( ( a ->1 b ) ->0 ( a ->2 b ) ) = 1$;
}
