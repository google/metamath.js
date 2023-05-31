include "wn.mm";
include "wo.mm";
include "ax-a4.mm";
include "ax-r1.mm";
include "ax-a2.mm";
include "ax-r2.mm";

theorem tt(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wva;
    wn;
    wo;
    #;
    @0;
    wvb;
    wvb;
    wn;
    wo;
    #;
    wo;
    #;
    @1;
    @0;
    @1;
    @0;
    wo;
    #;
    @2;
    @3;
    @0;
    @1;
    wva;
    ax-a4;
    ax-r1;
    @1;
    @0;
    ax-a2;
    ax-r2;
    @0;
    wvb;
    ax-a4;
    ax-r2;
  };

  return $|-$ $( a v a ' ) = ( b v b ' )$;
}
