include "wn.mm";
include "comcom2.mm";
include "comcom5.mm";

theorem comcom6(wva: $term$ a, wvb: $term$ b) {
  assume comcom6.1: $|- a ' C b$;





  do {
    wva;
    wvb;
    wva;
    wn;
    wvb;
    comcom6.1;
    comcom2;
    comcom5;
  };

  return $|-$ $a C b$;
}
