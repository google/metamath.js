include "wa.mm";
include "wo.mm";
include "wa2.mm";
include "wa5b.mm";
include "wr2.mm";
include "wdf-le1.mm";

theorem wlea(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    #;
    wva;
    @0;
    wva;
    wo;
    wva;
    @0;
    wo;
    wva;
    @0;
    wva;
    wa2;
    wva;
    wvb;
    wa5b;
    wr2;
    wdf-le1;
  };

  return $|-$ $( ( a ^ b ) =<2 a ) = 1$;
}
