include "wo.mm";
include "i3orcom.mm";
include "i3ror.mm";
include "binr2.mm";

theorem i3lor(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume i3lor.1: $|- ( a ->3 b ) = 1$;





  do {
    wvc;
    wva;
    wo;
    wva;
    wvc;
    wo;
    #;
    wvc;
    wvb;
    wo;
    #;
    wvc;
    wva;
    i3orcom;
    @0;
    wvb;
    wvc;
    wo;
    @1;
    wva;
    wvb;
    wvc;
    i3lor.1;
    i3ror;
    wvb;
    wvc;
    i3orcom;
    binr2;
    binr2;
  };

  return $|- ( ( c v a ) ->3 ( c v b ) ) = 1$;
}
