include "wa.mm";
include "wlea.mm";
include "wlecom.mm";

theorem wcoman1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    wva;
    wva;
    wvb;
    wlea;
    wlecom;
  };

  return $|- C ( ( a ^ b ) , a ) = 1$;
}
