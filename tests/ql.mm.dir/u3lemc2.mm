include "com2i3.mm";

theorem u3lemc2(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume ulemc2.1: $|- a C b$;
  assume ulemc2.2: $|- a C c$;





  do {
    wva;
    wvb;
    wvc;
    ulemc2.1;
    ulemc2.2;
    com2i3;
  };

  return $|- a C ( b ->3 c )$;
}
