include "wa.mm";
include "anass.mm";
include "bi1.mm";

theorem wanass(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wa;
    wvc;
    wa;
    wva;
    wvb;
    wvc;
    wa;
    wa;
    wva;
    wvb;
    wvc;
    anass;
    bi1;
  };

  return $|-$ $( ( ( a ^ b ) ^ c ) == ( a ^ ( b ^ c ) ) ) = 1$;
}
