include "wn.mm";
include "wa.mm";
include "wo.mm";
include "ax-a2.mm";
include "bi1.mm";
include "oran.mm";
include "wdf-le2.mm";
include "w3tr2.mm";
include "wcon3.mm";
include "wdf2le1.mm";

theorem wlecon(wva: $term$ a, wvb: $term$ b) {
  assume wle.1: $|- ( a =<2 b ) = 1$;





  do {
    wvb;
    wn;
    #;
    wva;
    wn;
    #;
    @0;
    @1;
    wa;
    #;
    wvb;
    wvb;
    wva;
    wo;
    #;
    wva;
    wvb;
    wo;
    #;
    @2;
    wn;
    #;
    wvb;
    @3;
    @4;
    wvb;
    wva;
    ax-a2;
    bi1;
    @3;
    @5;
    wvb;
    wva;
    oran;
    bi1;
    wva;
    wvb;
    wle.1;
    wdf-le2;
    w3tr2;
    wcon3;
    wdf2le1;
  };

  return $|- ( b ' =<2 a ' ) = 1$;
}
