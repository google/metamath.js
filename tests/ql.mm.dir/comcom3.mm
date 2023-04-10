include "wn.mm";
include "comcom.mm";
include "comcom2.mm";

theorem comcom3(wva: $term$ a, wvb: $term$ b) {
  assume comcom.1: $|- a C b$;





  do {
    wvb;
    wva;
    wn;
    wvb;
    wva;
    wva;
    wvb;
    comcom.1;
    comcom;
    comcom2;
    comcom;
  };

  return $|-$ $a ' C b$;
}
