include "u1lemc1.mm";

theorem u1lemc5(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wva;
    wvb;
    u1lemc1;
  };

  return $|- a C ( a ->1 b )$;
}
