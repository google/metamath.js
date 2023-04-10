include "wo.mm";
include "wa.mm";
include "fh2.mm";
include "ax-a2.mm";
include "lan.mm";
include "3tr1.mm";

theorem fh2c(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume fh.1: $|- a C b$;
  assume fh.2: $|- a C c$;





  do {
    wvb;
    wva;
    wvc;
    wo;
    #;
    wa;
    wvb;
    wva;
    wa;
    #;
    wvb;
    wvc;
    wa;
    #;
    wo;
    wvb;
    wvc;
    wva;
    wo;
    #;
    wa;
    @2;
    @1;
    wo;
    wva;
    wvb;
    wvc;
    fh.1;
    fh.2;
    fh2;
    @3;
    @0;
    wvb;
    wvc;
    wva;
    ax-a2;
    lan;
    @2;
    @1;
    ax-a2;
    3tr1;
  };

  return $|-$ $( b ^ ( c v a ) ) = ( ( b ^ c ) v ( b ^ a ) )$;
}
