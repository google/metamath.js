include "wn.mm";
include "ax-r4.mm";
include "ax-a1.mm";
include "ax-r1.mm";
include "ax-r2.mm";

theorem con2(wva: $term$ a, wvb: $term$ b) {
  assume con2.1: $|- a = b '$;





  do {
    wva;
    wn;
    wvb;
    wn;
    #;
    wn;
    #;
    wvb;
    wva;
    @0;
    con2.1;
    ax-r4;
    wvb;
    @1;
    wvb;
    ax-a1;
    ax-r1;
    ax-r2;
  };

  return $|- a ' = b$;
}
