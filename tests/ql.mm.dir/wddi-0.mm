include "wo.mm";
include "wa.mm";
include "wddi1.mm";
include "id5id0.mm";

theorem wddi-0(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





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
    wddi1;
    id5id0;
  };

  return $|-$ $( ( a ^ ( b v c ) ) ==0 ( ( a ^ b ) v ( a ^ c ) ) ) = 1$;
}
