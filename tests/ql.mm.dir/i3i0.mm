include "wn.mm";
include "wo.mm";
include "wi3.mm";
include "wt.mm";
include "lem4.mm";
include "ax-r1.mm";
include "ax-r2.mm";

theorem i3i0(wva: $term$ a, wvb: $term$ b) {
  assume i3i0.1: $|- ( a ->3 ( a ->3 b ) ) = 1$;





  do {
    wva;
    wn;
    wvb;
    wo;
    #;
    wva;
    wva;
    wvb;
    wi3;
    wi3;
    #;
    wt;
    @1;
    @0;
    wva;
    wvb;
    lem4;
    ax-r1;
    i3i0.1;
    ax-r2;
  };

  return $|- ( a ' v b ) = 1$;
}
