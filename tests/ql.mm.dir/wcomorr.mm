include "wo.mm";
include "wleo.mm";
include "wlecom.mm";

theorem wcomorr(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wo;
    wva;
    wvb;
    wleo;
    wlecom;
  };

  return $|- C ( a , ( a v b ) ) = 1$;
}
