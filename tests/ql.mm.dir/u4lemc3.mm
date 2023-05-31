include "u4lemc1.mm";

theorem u4lemc3(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wvb;
    wva;
    u4lemc1;
  };

  return $|-$ $a C ( b ->4 a )$;
}
