include "u2lemc1.mm";

theorem u2lemc3(wva: $term$ a, wvb: $term$ b) {
  assume ulemc3.1: $|- a C b$;





  do {
    wvb;
    wva;
    u2lemc1;
  };

  return $|- a C ( b ->2 a )$;
}
