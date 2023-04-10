include "comi31.mm";

theorem u3lemc5(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wva;
    wvb;
    comi31;
  };

  return $|-$ $a C ( a ->3 b )$;
}
