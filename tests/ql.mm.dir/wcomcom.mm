include "wcmtr.mm";
include "wt.mm";
include "cmtrcom.mm";
include "ax-r2.mm";

theorem wcomcom(wva: $term$ a, wvb: $term$ b) {
  assume wcomcom.1: $|- C ( a , b ) = 1$;





  do {
    wvb;
    wva;
    wcmtr;
    wva;
    wvb;
    wcmtr;
    wt;
    wvb;
    wva;
    cmtrcom;
    wcomcom.1;
    ax-r2;
  };

  return $|-$ $C ( b , a ) = 1$;
}
