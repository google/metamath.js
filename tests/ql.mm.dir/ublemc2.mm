include "tb.mm";
include "ublemc1.mm";
include "bicom.mm";
include "cbtr.mm";

theorem ublemc2(wva: $term$ a, wvb: $term$ b) {





  do {
    wvb;
    wvb;
    wva;
    tb;
    wva;
    wvb;
    tb;
    wvb;
    wva;
    ublemc1;
    wvb;
    wva;
    bicom;
    cbtr;
  };

  return $|- b C ( a == b )$;
}
