include "wt.mm";
include "wo.mm";
include "tb.mm";
include "le1.mm";
include "wr5-2v.mm";
include "ax-r1.mm";
include "bile.mm";
include "letr.mm";

theorem wom3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wom3.1: $|- ( a == b ) = 1$;





  do {
    wva;
    wt;
    wva;
    wvc;
    wo;
    wvb;
    wvc;
    wo;
    tb;
    #;
    wva;
    le1;
    wt;
    @0;
    @0;
    wt;
    wva;
    wvb;
    wvc;
    wom3.1;
    wr5-2v;
    ax-r1;
    bile;
    letr;
  };

  return $|-$ $a =< ( ( a v c ) == ( b v c ) )$;
}
