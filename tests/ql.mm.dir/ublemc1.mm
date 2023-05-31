include "combi.mm";

theorem ublemc1(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    combi;
  };

  return $|-$ $a C ( a == b )$;
}
