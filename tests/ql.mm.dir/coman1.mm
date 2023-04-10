include "wa.mm";
include "lea.mm";
include "lecom.mm";

theorem coman1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    wa;
    wva;
    wva;
    wvb;
    lea;
    lecom;
  };

  return $|- ( a ^ b ) C a$;
}
