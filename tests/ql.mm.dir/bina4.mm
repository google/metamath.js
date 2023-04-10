include "wo.mm";
include "leo.mm";
include "ax-a2.mm";
include "lbtr.mm";
include "lei3.mm";

theorem bina4(wva: $term$ a, wvb: $term$ b) {





  do {
    wvb;
    wva;
    wvb;
    wo;
    #;
    wvb;
    wvb;
    wva;
    wo;
    @0;
    wvb;
    wva;
    leo;
    wvb;
    wva;
    ax-a2;
    lbtr;
    lei3;
  };

  return $|- ( b ->3 ( a v b ) ) = 1$;
}
