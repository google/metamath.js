include "tb.mm";
include "wt.mm";
include "bi1.mm";
include "ax-r1.mm";

theorem 1bi(wva: $term$ a, wvb: $term$ b) {
  assume 1bi.1: $|- a = b$;





  do {
    wva;
    wvb;
    tb;
    wt;
    wva;
    wvb;
    1bi.1;
    bi1;
    ax-r1;
  };

  return $|- 1 = ( a == b )$;
}
