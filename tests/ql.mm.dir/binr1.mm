include "wn.mm";
include "i3le.mm";
include "lecon.mm";
include "lei3.mm";

theorem binr1(wva: $term$ a, wvb: $term$ b) {
  assume binr1.1: $|- ( a ->3 b ) = 1$;





  do {
    wvb;
    wn;
    wva;
    wn;
    wva;
    wvb;
    wva;
    wvb;
    binr1.1;
    i3le;
    lecon;
    lei3;
  };

  return $|- ( b ' ->3 a ' ) = 1$;
}
