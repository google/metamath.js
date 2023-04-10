include "tb.mm";
include "lbi.mm";
include "rbi.mm";
include "ax-r2.mm";

theorem 2bi(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {
  assume 2bi.1: $|- a = b$;
  assume 2bi.2: $|- c = d$;





  do {
    wva;
    wvc;
    tb;
    wva;
    wvd;
    tb;
    wvb;
    wvd;
    tb;
    wvc;
    wvd;
    wva;
    2bi.2;
    lbi;
    wva;
    wvb;
    wvd;
    2bi.1;
    rbi;
    ax-r2;
  };

  return $|-$ $( a == c ) = ( b == d )$;
}
