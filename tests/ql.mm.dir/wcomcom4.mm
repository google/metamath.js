include "wn.mm";
include "wcomcom3.mm";
include "wcomcom2.mm";

theorem wcomcom4(wva: $term$ a, wvb: $term$ b) {
  assume wcomcom.1: $|- C ( a , b ) = 1$;





  do {
    wva;
    wn;
    wvb;
    wva;
    wvb;
    wcomcom.1;
    wcomcom3;
    wcomcom2;
  };

  return $|- C ( a ' , b ' ) = 1$;
}
