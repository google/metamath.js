include "wn.mm";
include "comcom3.mm";
include "comcom5.mm";

theorem comcom7(wva: $term$ a, wvb: $term$ b) {
  assume comcom7.1: $|- a C b '$;





  do {
    wva;
    wvb;
    wva;
    wvb;
    wn;
    comcom7.1;
    comcom3;
    comcom5;
  };

  return $|- a C b$;
}
