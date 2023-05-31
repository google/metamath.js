include "wi1.mm";
include "wn.mm";
include "wa.mm";
include "wo.mm";
include "wt.mm";
include "df-i1.mm";
include "id.mm";
include "ax-a2.mm";
include "ax-r5.mm";
include "ax-r1.mm";
include "3tr.mm";
include "wql2lem2.mm";
include "skr0.mm";

theorem wql2lem4(wva: $term$ a, wvb: $term$ b) {
  assume wql2lem4.1: $|- ( ( ( a ^ b ' ) v ( a ^ b ) ) ->2 ( a ' v ( a ^ b ) ) ) = 1$;
  assume wql2lem4.2: $|- ( ( a ->1 b ) v ( a ^ b ' ) ) = 1$;





  do {
    wva;
    wvb;
    wi1;
    #;
    wva;
    wn;
    #;
    wva;
    wvb;
    wa;
    #;
    wo;
    #;
    @3;
    wt;
    wva;
    wvb;
    df-i1;
    #;
    @3;
    id;
    wva;
    wvb;
    wn;
    wa;
    #;
    @3;
    wo;
    #;
    @3;
    @6;
    @3;
    @5;
    wo;
    #;
    @0;
    @5;
    wo;
    #;
    wt;
    @5;
    @3;
    ax-a2;
    @8;
    @7;
    @0;
    @3;
    @5;
    @4;
    ax-r5;
    ax-r1;
    wql2lem4.2;
    3tr;
    @5;
    @1;
    @2;
    wql2lem4.1;
    wql2lem2;
    skr0;
    3tr;
  };

  return $|-$ $( a ->1 b ) = 1$;
}
