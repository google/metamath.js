include "wn.mm";
include "wo.mm";
include "i3i0.mm";
include "binr1.mm";
include "i3ror.mm";
include "skmp3.mm";
include "i0i3.mm";

theorem i3i0tr(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume i3i0tr.1: $|- ( a ->3 b ) = 1$;
  assume i3i0tr.2: $|- ( b ->3 ( b ->3 c ) ) = 1$;





  do {
    wva;
    wvc;
    wvb;
    wn;
    #;
    wvc;
    wo;
    wva;
    wn;
    #;
    wvc;
    wo;
    wvb;
    wvc;
    i3i0tr.2;
    i3i0;
    @0;
    @1;
    wvc;
    wva;
    wvb;
    i3i0tr.1;
    binr1;
    i3ror;
    skmp3;
    i0i3;
  };

  return $|- ( a ->3 ( a ->3 c ) ) = 1$;
}
