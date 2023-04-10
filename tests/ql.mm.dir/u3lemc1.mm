include "comi31.mm";

theorem u3lemc1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    comi31;
  };

  return $|- a C ( a ->3 b )$;
}
