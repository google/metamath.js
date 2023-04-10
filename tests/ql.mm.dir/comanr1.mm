include "wa.mm";
include "coman1.mm";
include "comcom.mm";

theorem comanr1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    wva;
    wva;
    wvb;
    coman1;
    comcom;
  };

  return $|-$ $a C ( a ^ b )$;
}
