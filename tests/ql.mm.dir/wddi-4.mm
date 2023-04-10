include "wo.mm";
include "wa.mm";
include "wddi-0.mm";
include "wdid0id4.mm";

theorem wddi-4(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





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
    wdid0id4;
  };

  return $|- ( ( a ^ ( b v c ) ) ==4 ( ( a ^ b ) v ( a ^ c ) ) ) = 1$;
}
