include "wa.mm";
include "an12.mm";
include "lan.mm";
include "anass.mm";
include "3tr1.mm";

theorem an4(wva: $term$ a, wvb: $term$ b, wvc: $term$ c, wvd: $term$ d) {





  do {
    wva;
    wvb;
    wvc;
    wvd;
    wa;
    #;
    wa;
    #;
    wa;
    wva;
    wvc;
    wvb;
    wvd;
    wa;
    #;
    wa;
    #;
    wa;
    wva;
    wvb;
    wa;
    @0;
    wa;
    wva;
    wvc;
    wa;
    @2;
    wa;
    @1;
    @3;
    wva;
    wvb;
    wvc;
    wvd;
    an12;
    lan;
    wva;
    wvb;
    @0;
    anass;
    wva;
    wvc;
    @2;
    anass;
    3tr1;
  };

  return $|- ( ( a ^ b ) ^ ( c ^ d ) ) = ( ( a ^ c ) ^ ( b ^ d ) )$;
}
