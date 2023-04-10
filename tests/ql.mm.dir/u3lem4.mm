include "wi3.mm";
include "wn.mm";
include "wo.mm";
include "wt.mm";
include "lem4.mm";
include "ax-a2.mm";
include "u3lemonb.mm";
include "ax-r2.mm";

theorem u3lem4(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wva;
    wi3;
    #;
    wi3;
    wi3;
    wva;
    wn;
    #;
    @0;
    wo;
    #;
    wt;
    wva;
    @0;
    lem4;
    @2;
    @0;
    @1;
    wo;
    wt;
    @1;
    @0;
    ax-a2;
    wvb;
    wva;
    u3lemonb;
    ax-r2;
    ax-r2;
  };

  return $|- ( a ->3 ( a ->3 ( b ->3 a ) ) ) = 1$;
}
