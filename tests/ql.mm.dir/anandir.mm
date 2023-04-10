include "wa.mm";
include "anidm.mm";
include "ax-r1.mm";
include "lan.mm";
include "an4.mm";
include "ax-r2.mm";

theorem anandir(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wa;
    #;
    wvc;
    wa;
    @0;
    wvc;
    wvc;
    wa;
    #;
    wa;
    wva;
    wvc;
    wa;
    wvb;
    wvc;
    wa;
    wa;
    wvc;
    @1;
    @0;
    @1;
    wvc;
    wvc;
    anidm;
    ax-r1;
    lan;
    wva;
    wvb;
    wvc;
    wvc;
    an4;
    ax-r2;
  };

  return $|-$ $( ( a ^ b ) ^ c ) = ( ( a ^ c ) ^ ( b ^ c ) )$;
}
