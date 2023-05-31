include "wa.mm";
include "wo.mm";
include "fh4.mm";
include "ancom.mm";
include "lor.mm";
include "3tr1.mm";

theorem fh4c(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume fh.1: $|- a C b$;
  assume fh.2: $|- a C c$;





  do {
    wvb;
    wva;
    wvc;
    wa;
    #;
    wo;
    wvb;
    wva;
    wo;
    #;
    wvb;
    wvc;
    wo;
    #;
    wa;
    wvb;
    wvc;
    wva;
    wa;
    #;
    wo;
    @2;
    @1;
    wa;
    wva;
    wvb;
    wvc;
    fh.1;
    fh.2;
    fh4;
    @3;
    @0;
    wvb;
    wvc;
    wva;
    ancom;
    lor;
    @2;
    @1;
    ancom;
    3tr1;
  };

  return $|-$ $( b v ( c ^ a ) ) = ( ( b v c ) ^ ( b v a ) )$;
}
