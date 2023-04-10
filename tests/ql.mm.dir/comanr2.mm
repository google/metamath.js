include "wa.mm";
include "coman2.mm";
include "comcom.mm";

theorem comanr2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    wvb;
    wva;
    wvb;
    coman2;
    comcom;
  };

  return $|- b C ( a ^ b )$;
}
