include "comi32.mm";

theorem u3lemc3(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wva;
    wvb;
    ulemc3.1;
    comi32;
  };

  return $|-$ $a C ( b ->3 a )$;
}
