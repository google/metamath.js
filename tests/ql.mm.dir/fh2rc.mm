include "wo.mm";
include "wa.mm";
include "fh2r.mm";
include "ax-a2.mm";
include "ran.mm";
include "3tr1.mm";

theorem fh2rc(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume fh.1: $|- a C b$;
  assume fh.2: $|- a C c$;





  do {
    wva;
    wvc;
    wo;
    #;
    wvb;
    wa;
    wva;
    wvb;
    wa;
    #;
    wvc;
    wvb;
    wa;
    #;
    wo;
    wvc;
    wva;
    wo;
    #;
    wvb;
    wa;
    @2;
    @1;
    wo;
    wva;
    wvb;
    wvc;
    fh.1;
    fh.2;
    fh2r;
    @3;
    @0;
    wvb;
    wvc;
    wva;
    ax-a2;
    ran;
    @2;
    @1;
    ax-a2;
    3tr1;
  };

  return $|- ( ( c v a ) ^ b ) = ( ( c ^ b ) v ( a ^ b ) )$;
}
