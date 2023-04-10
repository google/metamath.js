include "woml.mm";

theorem ska11(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    woml;
  };

  return $|-$ $( ( a v ( a ' ^ ( a v b ) ) ) == ( a v b ) ) = 1$;
}
