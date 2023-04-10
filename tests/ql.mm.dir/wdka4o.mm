include "wo.mm";
include "wdid0id5.mm";
include "wr5.mm";
include "id5id0.mm";

theorem wdka4o(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume wdid0id5.1: $|- ( a ==0 b ) = 1$;





  do {
    wva;
    wvc;
    wo;
    wvb;
    wvc;
    wo;
    wva;
    wvb;
    wvc;
    wva;
    wvb;
    wdid0id5.1;
    wdid0id5;
    wr5;
    id5id0;
  };

  return $|- ( ( a v c ) ==0 ( b v c ) ) = 1$;
}
