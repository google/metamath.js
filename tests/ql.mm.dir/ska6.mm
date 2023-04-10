include "wa.mm";
include "anass.mm";
include "ax-r1.mm";
include "bi1.mm";

theorem ska6(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wvc;
    wa;
    wa;
    #;
    wva;
    wvb;
    wa;
    wvc;
    wa;
    #;
    @1;
    @0;
    wva;
    wvb;
    wvc;
    anass;
    ax-r1;
    bi1;
  };

  return $|- ( ( a ^ ( b ^ c ) ) == ( ( a ^ b ) ^ c ) ) = 1$;
}
