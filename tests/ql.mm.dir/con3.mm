include "wn.mm";
include "ax-a1.mm";
include "ax-r4.mm";
include "ax-r2.mm";

theorem con3(wva: $term$ a, wvb: $term$ b) {
  assume con3.1: $|- a ' = b$;





  do {
    wva;
    wva;
    wn;
    #;
    wn;
    wvb;
    wn;
    wva;
    ax-a1;
    @0;
    wvb;
    con3.1;
    ax-r4;
    ax-r2;
  };

  return $|-$ $a = b '$;
}
