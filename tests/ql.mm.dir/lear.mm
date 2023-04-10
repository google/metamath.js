include "wa.mm";
include "ancom.mm";
include "lea.mm";
include "bltr.mm";

theorem lear(wva: $term$ a, wvb: $term$ b) {





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
    lea;
    bltr;
  };

  return $|- ( a ^ b ) =< b$;
}
