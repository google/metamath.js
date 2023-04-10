include "wa.mm";
include "ancom.mm";
include "coman1.mm";
include "bctr.mm";

theorem coman2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    wvb;
    wva;
    wa;
    wvb;
    wva;
    wvb;
    ancom;
    wvb;
    wva;
    coman1;
    bctr;
  };

  return $|-$ $( a ^ b ) C b$;
}
