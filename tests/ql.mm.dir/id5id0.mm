include "tb.mm";
include "wid0.mm";
include "id5leid0.mm";
include "sklem.mm";
include "skr0.mm";

theorem id5id0(wva: $term$ a, wvb: $term$ b) {
  assume id5id0.1: $|- ( a == b ) = 1$;





  do {
    wva;
    wvb;
    tb;
    #;
    wva;
    wvb;
    wid0;
    #;
    id5id0.1;
    @0;
    @1;
    wva;
    wvb;
    id5leid0;
    sklem;
    skr0;
  };

  return $|- ( a ==0 b ) = 1$;
}
