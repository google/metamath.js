include "wo.mm";
include "wa.mm";
include "fh1r.mm";
include "ax-a2.mm";
include "ran.mm";
include "3tr1.mm";

theorem fh1rc(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume fh.1: $|- a C b$;
  assume fh.2: $|- a C c$;





  do {
    wvb;
    wvc;
    wo;
    #;
    wva;
    wa;
    wvb;
    wva;
    wa;
    #;
    wvc;
    wva;
    wa;
    #;
    wo;
    wvc;
    wvb;
    wo;
    #;
    wva;
    wa;
    @2;
    @1;
    wo;
    wva;
    wvb;
    wvc;
    fh.1;
    fh.2;
    fh1r;
    @3;
    @0;
    wva;
    wvc;
    wvb;
    ax-a2;
    ran;
    @2;
    @1;
    ax-a2;
    3tr1;
  };

  return $|- ( ( c v b ) ^ a ) = ( ( c ^ a ) v ( b ^ a ) )$;
}
