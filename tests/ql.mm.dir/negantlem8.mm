include "wn.mm";
include "wa.mm";
include "wo.mm";
include "negantlem6.mm";
include "ax-r4.mm";
include "oran2.mm";
include "3tr1.mm";

theorem negantlem8(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume negant.1: $|- ( a ->1 c ) = ( b ->1 c )$;





  do {
    wva;
    wvc;
    wn;
    #;
    wa;
    #;
    wn;
    wvb;
    @0;
    wa;
    #;
    wn;
    wva;
    wn;
    wvc;
    wo;
    wvb;
    wn;
    wvc;
    wo;
    @1;
    @2;
    wva;
    wvb;
    wvc;
    negant.1;
    negantlem6;
    ax-r4;
    wva;
    wvc;
    oran2;
    wvb;
    wvc;
    oran2;
    3tr1;
  };

  return $|-$ $( a ' v c ) = ( b ' v c )$;
}
