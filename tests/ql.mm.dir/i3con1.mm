include "wn.mm";
include "binr1.mm";
include "ax-a1.mm";
include "i33tr1.mm";

theorem i3con1(wva: $term$ a, wvb: $term$ b) {
  assume i3con1.1: $|- ( a ' ->3 b ' ) = 1$;





  do {
    wvb;
    wn;
    #;
    wn;
    wva;
    wn;
    #;
    wn;
    wvb;
    wva;
    @1;
    @0;
    i3con1.1;
    binr1;
    wvb;
    ax-a1;
    wva;
    ax-a1;
    i33tr1;
  };

  return $|- ( b ->3 a ) = 1$;
}
