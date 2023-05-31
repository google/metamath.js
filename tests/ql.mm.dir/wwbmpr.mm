include "wr1.mm";
include "wwbmp.mm";

theorem wwbmpr(wva: $term$ a, wvb: $term$ b) {
  assume wwbmpr.1: $|- b = 1$;
  assume wwbmpr.2: $|- ( a == b ) = 1$;





  do {
    wvb;
    wva;
    wwbmpr.1;
    wva;
    wvb;
    wwbmpr.2;
    wr1;
    wwbmp;
  };

  return $|-$ $a = 1$;
}
