include "wo.mm";
include "wlor.mm";
include "wr5-2v.mm";
include "wr2.mm";

theorem w2or(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume w2or.1: $|- ( a == b ) = 1$;
  assume w2or.2: $|- ( c == d ) = 1$;





  do {
    wva;
    wvc;
    wo;
    wva;
    wvd;
    wo;
    wvb;
    wvd;
    wo;
    wvc;
    wvd;
    wva;
    w2or.2;
    wlor;
    wva;
    wvb;
    wvd;
    w2or.1;
    wr5-2v;
    wr2;
  };

  return $|- ( ( a v c ) == ( b v d ) ) = 1$;
}
