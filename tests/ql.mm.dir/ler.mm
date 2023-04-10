include "wo.mm";
include "ax-a3.mm";
include "ax-r1.mm";
include "df-le2.mm";
include "ax-r5.mm";
include "ax-r2.mm";
include "df-le1.mm";

theorem ler(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume le.1: $|- a =< b$;





  do {
    wva;
    wvb;
    wvc;
    wo;
    #;
    wva;
    @0;
    wo;
    #;
    wva;
    wvb;
    wo;
    #;
    wvc;
    wo;
    #;
    @0;
    @3;
    @1;
    wva;
    wvb;
    wvc;
    ax-a3;
    ax-r1;
    @2;
    wvb;
    wvc;
    wva;
    wvb;
    le.1;
    df-le2;
    ax-r5;
    ax-r2;
    df-le1;
  };

  return $|- a =< ( b v c )$;
}
