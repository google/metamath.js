include "wo.mm";
include "oridm.mm";
include "ax-r1.mm";
include "ax-r5.mm";
include "or4.mm";
include "ax-r2.mm";

theorem orordi(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wvc;
    wo;
    #;
    wo;
    wva;
    wva;
    wo;
    #;
    @0;
    wo;
    wva;
    wvb;
    wo;
    wva;
    wvc;
    wo;
    wo;
    wva;
    @1;
    @0;
    @1;
    wva;
    wva;
    oridm;
    ax-r1;
    ax-r5;
    wva;
    wva;
    wvb;
    wvc;
    or4;
    ax-r2;
  };

  return $|- ( a v ( b v c ) ) = ( ( a v b ) v ( a v c ) )$;
}
