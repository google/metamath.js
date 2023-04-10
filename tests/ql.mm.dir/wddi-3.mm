include "wo.mm";
include "wa.mm";
include "wddi-0.mm";
include "wdid0id3.mm";

theorem wddi-3(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wvc;
    wo;
    wa;
    wva;
    wvb;
    wa;
    wva;
    wvc;
    wa;
    wo;
    wva;
    wvb;
    wvc;
    wddi-0;
    wdid0id3;
  };

  return $|- ( ( a ^ ( b v c ) ) ==3 ( ( a ^ b ) v ( a ^ c ) ) ) = 1$;
}
