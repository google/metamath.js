include "wn.mm";
include "wcomcom.mm";
include "wcomcom2.mm";

theorem wcomcom3(wva: $term$ a, wvb: $term$ b) {
  assume wcomcom.1: $|- C ( a , b ) = 1$;





  do {
    wvb;
    wva;
    wn;
    wvb;
    wva;
    wva;
    wvb;
    wcomcom.1;
    wcomcom;
    wcomcom2;
    wcomcom;
  };

  return $|-$ $C ( a ' , b ) = 1$;
}
