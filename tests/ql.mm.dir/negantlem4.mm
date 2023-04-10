include "wn.mm";
include "wi1.mm";
include "wa.mm";
include "wo.mm";
include "df-i1.mm";
include "ax-a1.mm";
include "ax-r5.mm";
include "ax-r1.mm";
include "ax-r2.mm";
include "negantlem2.mm";
include "negantlem3.mm";
include "lel2or.mm";
include "bltr.mm";

theorem negantlem4(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume negant.1: $|- ( a ->1 c ) = ( b ->1 c )$;





  do {
    wva;
    wn;
    #;
    wvc;
    wi1;
    #;
    wva;
    @0;
    wvc;
    wa;
    #;
    wo;
    #;
    wvb;
    wn;
    wvc;
    wi1;
    #;
    @1;
    @0;
    wn;
    #;
    @2;
    wo;
    #;
    @3;
    @0;
    wvc;
    df-i1;
    @3;
    @6;
    wva;
    @5;
    @2;
    wva;
    ax-a1;
    ax-r5;
    ax-r1;
    ax-r2;
    wva;
    @4;
    @2;
    wva;
    wvb;
    wvc;
    negant.1;
    negantlem2;
    wva;
    wvb;
    wvc;
    negant.1;
    negantlem3;
    lel2or;
    bltr;
  };

  return $|-$ $( a ' ->1 c ) =< ( b ' ->1 c )$;
}
