include "wt.mm";
include "tb.mm";
include "1b.mm";
include "ax-r1.mm";
include "ax-r2.mm";

theorem wr3(wva: $term$ a) {
  assume wr3.1: $|- ( 1 == a ) = 1$;





  do {
    wva;
    wt;
    wva;
    tb;
    #;
    wt;
    @0;
    wva;
    wva;
    1b;
    ax-r1;
    wr3.1;
    ax-r2;
  };

  return $|-$ $a = 1$;
}
