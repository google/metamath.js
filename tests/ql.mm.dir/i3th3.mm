include "wn.mm";
include "wi3.mm";
include "wo.mm";
include "wt.mm";
include "lem4.mm";
include "li3.mm";
include "bina3.mm";
include "ax-r2.mm";

theorem i3th3(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wn;
    #;
    wva;
    wva;
    wvb;
    wi3;
    wi3;
    #;
    wi3;
    @0;
    @0;
    wvb;
    wo;
    #;
    wi3;
    wt;
    @1;
    @2;
    @0;
    wva;
    wvb;
    lem4;
    li3;
    @0;
    wvb;
    bina3;
    ax-r2;
  };

  return $|-$ $( a ' ->3 ( a ->3 ( a ->3 b ) ) ) = 1$;
}
