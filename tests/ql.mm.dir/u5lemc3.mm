include "u5lemc1b.mm";

theorem u5lemc3(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wvb;
    wva;
    u5lemc1b;
  };

  return $|- a C ( b ->5 a )$;
}
