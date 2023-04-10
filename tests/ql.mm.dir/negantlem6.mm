include "wn.mm";
include "wa.mm";
include "negant.mm";
include "negantlem5.mm";
include "ax-a1.mm";
include "ran.mm";
include "3tr1.mm";

theorem negantlem6(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume negant.1: $|- ( a ->1 c ) = ( b ->1 c )$;





  do {
    wva;
    wn;
    #;
    wn;
    #;
    wvc;
    wn;
    #;
    wa;
    wvb;
    wn;
    #;
    wn;
    #;
    @2;
    wa;
    wva;
    @2;
    wa;
    wvb;
    @2;
    wa;
    @0;
    @3;
    wvc;
    wva;
    wvb;
    wvc;
    negant.1;
    negant;
    negantlem5;
    wva;
    @1;
    @2;
    wva;
    ax-a1;
    ran;
    wvb;
    @4;
    @2;
    wvb;
    ax-a1;
    ran;
    3tr1;
  };

  return $|- ( a ^ c ' ) = ( b ^ c ' )$;
}
