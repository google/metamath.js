include "wid5.mm";
include "wi2.mm";
include "wt.mm";
include "lem3.3.4.mm";
include "ax-r1.mm";
include "lem3.4.3.mm";
include "ax-r2.mm";

theorem lem3.4.4(wva: $term$ a, wvb: $term$ b) {
  assume lem3.4.4.1: $|- ( a ->2 b ) = 1$;
  assume lem3.4.4.2: $|- ( b ->2 a ) = 1$;





  do {
    wva;
    wvb;
    wid5;
    #;
    wva;
    @0;
    wi2;
    #;
    wt;
    @1;
    @0;
    wva;
    wvb;
    lem3.4.4.2;
    lem3.3.4;
    ax-r1;
    wva;
    wvb;
    lem3.4.4.1;
    lem3.4.3;
    ax-r2;
  };

  return $|-$ $( a ==5 b ) = 1$;
}
