include "wn.mm";
include "comcom3.mm";
include "comcom2.mm";

theorem comcom4(wva: $term$ a, wvb: $term$ b) {
  assume comcom.1: $|- a C b$;





  do {
    wva;
    wn;
    wvb;
    wva;
    wvb;
    comcom.1;
    comcom3;
    comcom2;
  };

  return $|- a ' C b '$;
}
