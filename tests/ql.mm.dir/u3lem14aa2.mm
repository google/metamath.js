include "wn.mm";
include "wi3.mm";
include "wt.mm";
include "wi1.mm";
include "u3lem13a.mm";
include "u3lem13b.mm";
include "ax-r1.mm";
include "ax-r2.mm";
include "ud3lem0a.mm";
include "u3lem14aa.mm";

theorem u3lem14aa2(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wvb;
    wvb;
    wva;
    wn;
    wi3;
    #;
    wn;
    wi3;
    #;
    wi3;
    #;
    wi3;
    wva;
    wva;
    @0;
    wvb;
    wn;
    wi3;
    #;
    wi3;
    #;
    wi3;
    wt;
    @2;
    @4;
    wva;
    @1;
    @3;
    wva;
    @1;
    wvb;
    wva;
    wi1;
    #;
    @3;
    wvb;
    wva;
    u3lem13a;
    @3;
    @5;
    wvb;
    wva;
    u3lem13b;
    ax-r1;
    ax-r2;
    ud3lem0a;
    ud3lem0a;
    wva;
    wvb;
    u3lem14aa;
    ax-r2;
  };

  return $|-$ $( a ->3 ( a ->3 ( b ->3 ( b ->3 a ' ) ' ) ) ) = 1$;
}
