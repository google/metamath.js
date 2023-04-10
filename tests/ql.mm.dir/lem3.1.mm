include "tb.mm";
include "wt.mm";
include "wlem3.1.mm";
include "ax-r1.mm";
include "r3a.mm";

theorem lem3.1(wva: $term$ a, wvb: $term$ b) {
  assume lem3.1.1: $|- ( a v b ) = b$;
  assume lem3.1.2: $|- ( b ' v a ) = 1$;





  do {
    wva;
    wvb;
    wva;
    wvb;
    tb;
    wt;
    wva;
    wvb;
    lem3.1.1;
    lem3.1.2;
    wlem3.1;
    ax-r1;
    r3a;
  };

  return $|-$ $a = b$;
}
