include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wi1.mm";
include "leo.mm";
include "df-i1.mm";
include "ax-r1.mm";
include "lbtr.mm";

theorem u1lem9b(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    @0;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    wva;
    wvb;
    wi1;
    #;
    @0;
    @1;
    leo;
    @3;
    @2;
    wva;
    wvb;
    df-i1;
    ax-r1;
    lbtr;
  };

  return $|- a ' =< ( a ->1 b )$;
}
