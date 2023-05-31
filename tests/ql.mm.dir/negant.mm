include "wn.mm";
include "wi1.mm";
include "negantlem4.mm";
include "ax-r1.mm";
include "lebi.mm";

theorem negant(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume negant.1: $|- ( a ->1 c ) = ( b ->1 c )$;





  do {
    wva;
    wn;
    wvc;
    wi1;
    wvb;
    wn;
    wvc;
    wi1;
    wva;
    wvb;
    wvc;
    negant.1;
    negantlem4;
    wvb;
    wva;
    wvc;
    wva;
    wvc;
    wi1;
    wvb;
    wvc;
    wi1;
    negant.1;
    ax-r1;
    negantlem4;
    lebi;
  };

  return $|-$ $( a ' ->1 c ) = ( b ' ->1 c )$;
}
