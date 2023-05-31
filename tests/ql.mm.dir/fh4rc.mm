include "wa.mm";
include "wo.mm";
include "fh4r.mm";
include "ancom.mm";
include "ax-r5.mm";
include "3tr1.mm";

theorem fh4rc(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume fh.1: $|- a C b$;
  assume fh.2: $|- a C c$;





  do {
    wva;
    wvc;
    wa;
    #;
    wvb;
    wo;
    wva;
    wvb;
    wo;
    #;
    wvc;
    wvb;
    wo;
    #;
    wa;
    wvc;
    wva;
    wa;
    #;
    wvb;
    wo;
    @2;
    @1;
    wa;
    wva;
    wvb;
    wvc;
    fh.1;
    fh.2;
    fh4r;
    @3;
    @0;
    wvb;
    wvc;
    wva;
    ancom;
    ax-r5;
    @2;
    @1;
    ancom;
    3tr1;
  };

  return $|-$ $( ( c ^ a ) v b ) = ( ( c v b ) ^ ( a v b ) )$;
}
