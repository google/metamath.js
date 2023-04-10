include "wt.mm";
include "tb.mm";
include "1bi.mm";
include "ax-r2.mm";
include "r3a.mm";

theorem wed(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume wed.1: $|- a = b$;
  assume wed.2: $|- ( a == b ) = ( c == d )$;





  do {
    wvc;
    wvd;
    wt;
    wva;
    wvb;
    tb;
    wvc;
    wvd;
    tb;
    wva;
    wvb;
    wed.1;
    1bi;
    wed.2;
    ax-r2;
    r3a;
  };

  return $|-$ $c = d$;
}
