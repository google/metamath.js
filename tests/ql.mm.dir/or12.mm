include "wo.mm";
include "ax-a2.mm";
include "ax-r5.mm";
include "ax-a3.mm";
include "3tr2.mm";

theorem or12(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wo;
    #;
    wvc;
    wo;
    wvb;
    wva;
    wo;
    #;
    wvc;
    wo;
    wva;
    wvb;
    wvc;
    wo;
    wo;
    wvb;
    wva;
    wvc;
    wo;
    wo;
    @0;
    @1;
    wvc;
    wva;
    wvb;
    ax-a2;
    ax-r5;
    wva;
    wvb;
    wvc;
    ax-a3;
    wvb;
    wva;
    wvc;
    ax-a3;
    3tr2;
  };

  return $|- ( a v ( b v c ) ) = ( b v ( a v c ) )$;
}
