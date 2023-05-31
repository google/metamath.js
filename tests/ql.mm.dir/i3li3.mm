include "wi3.mm";
include "i3le.mm";
include "lebi.mm";
include "li3.mm";
include "bile.mm";
include "lei3.mm";

theorem i3li3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume i3li3.1: $|- ( a ->3 b ) = 1$;
  assume i3li3.2: $|- ( b ->3 a ) = 1$;





  do {
    wvc;
    wva;
    wi3;
    #;
    wvc;
    wvb;
    wi3;
    #;
    @0;
    @1;
    wva;
    wvb;
    wvc;
    wva;
    wvb;
    wva;
    wvb;
    i3li3.1;
    i3le;
    wvb;
    wva;
    i3li3.2;
    i3le;
    lebi;
    li3;
    bile;
    lei3;
  };

  return $|-$ $( ( c ->3 a ) ->3 ( c ->3 b ) ) = 1$;
}
