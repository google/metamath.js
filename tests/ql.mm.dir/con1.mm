include "wn.mm";
include "ax-r4.mm";
include "ax-a1.mm";
include "3tr1.mm";

theorem con1(wva: $term$ a, wvb: $term$ b) {
  assume con1.1: $|- a ' = b '$;





  do {
    wva;
    wn;
    #;
    wn;
    wvb;
    wn;
    #;
    wn;
    wva;
    wvb;
    @0;
    @1;
    con1.1;
    ax-r4;
    wva;
    ax-a1;
    wvb;
    ax-a1;
    3tr1;
  };

  return $|-$ $a = b$;
}
