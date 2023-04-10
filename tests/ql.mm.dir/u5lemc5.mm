include "u5lemc1.mm";

theorem u5lemc5(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wva;
    wvb;
    u5lemc1;
  };

  return $|-$ $a C ( a ->5 b )$;
}
