include "wi3.mm";
include "i3le.mm";
include "lebi.mm";
include "2i3.mm";
include "bile.mm";
include "lei3.mm";

theorem i32i3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume i32i3.1: $|- ( a ->3 b ) = 1$;
  assume i32i3.2: $|- ( b ->3 a ) = 1$;
  assume i32i3.3: $|- ( c ->3 d ) = 1$;
  assume i32i3.4: $|- ( d ->3 c ) = 1$;





  do {
    wva;
    wvc;
    wi3;
    #;
    wvb;
    wvd;
    wi3;
    #;
    @0;
    @1;
    wva;
    wvb;
    wvc;
    wvd;
    wva;
    wvb;
    wva;
    wvb;
    i32i3.1;
    i3le;
    wvb;
    wva;
    i32i3.2;
    i3le;
    lebi;
    wvc;
    wvd;
    wvc;
    wvd;
    i32i3.3;
    i3le;
    wvd;
    wvc;
    i32i3.4;
    i3le;
    lebi;
    2i3;
    bile;
    lei3;
  };

  return $|- ( ( a ->3 c ) ->3 ( b ->3 d ) ) = 1$;
}
