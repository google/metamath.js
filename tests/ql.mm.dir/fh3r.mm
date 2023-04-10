include "wa.mm";
include "wo.mm";
include "fh3.mm";
include "ax-a2.mm";
include "2an.mm";
include "3tr1.mm";

theorem fh3r(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume fh.1: $|- a C b$;
  assume fh.2: $|- a C c$;





  do {
    wva;
    wvb;
    wvc;
    wa;
    #;
    wo;
    wva;
    wvb;
    wo;
    #;
    wva;
    wvc;
    wo;
    #;
    wa;
    @0;
    wva;
    wo;
    wvb;
    wva;
    wo;
    #;
    wvc;
    wva;
    wo;
    #;
    wa;
    wva;
    wvb;
    wvc;
    fh.1;
    fh.2;
    fh3;
    @0;
    wva;
    ax-a2;
    @3;
    @1;
    @4;
    @2;
    wvb;
    wva;
    ax-a2;
    wvc;
    wva;
    ax-a2;
    2an;
    3tr1;
  };

  return $|-$ $( ( b ^ c ) v a ) = ( ( b v a ) ^ ( c v a ) )$;
}
